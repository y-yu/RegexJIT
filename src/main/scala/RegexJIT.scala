import org.objectweb.asm._
import org.objectweb.asm.Opcodes._

/**
 * Created by hikaru_yoshimura on 2015/05/14.
 */

sealed trait Regex
case object Empty                  extends Regex
case class Let(c: Char)            extends Regex
case class Con(a: Regex, b: Regex) extends Regex
case class Alt(a: Regex, b: Regex) extends Regex
case class Star(a: Regex)          extends Regex

sealed trait LId
case class LInt(n: Int)   extends LId
case class LLbl(l: Label) extends LId

sealed trait Repr
case object Const1             extends Repr
case class  Push(n: Int)       extends Repr
case object Dup2               extends Repr
case class  Lbl(l: LId)     extends Repr
case object Add                extends Repr
case class  Goto(l: LId)    extends Repr
case class  IfTrue(l: LId)  extends Repr
case class  IfCmpNe(l: LId) extends Repr
case class  InvokeStatic(p: String, n: String, t: String)  extends Repr
case class  InvokeVirtual(p: String, n: String, t: String) extends Repr

class DynamicClassLoader extends ClassLoader {
  def define(className: String, bytecode: Array[Byte]) =
    super.defineClass(className, bytecode, 0, bytecode.length)
}

object RegexJIT {
  val cname = "RegexJITCompiler"
  val mname = "test"
  val mtype = "(Ljava/lang/String;II)Z"

  val lmiss  = LLbl(new Label())
  val lmatch = LLbl(new Label())

  def mk_label(n: Int): (LId, Int) = (LInt(n), n + 1)

  def compile(re: Regex): List[Repr] = {
    def loop(re: Regex, n: Int): (List[Repr], Int) = re match {
      case Empty => (Nil, n)
      case Let(c) =>
        val (l1, n1) = mk_label(n)
        val r = List(
          Lbl(l1),
          Dup2,
          InvokeVirtual("java/lang/String", "charAt", "(I)C"),
          Push(c.toInt),
          IfCmpNe(lmiss),
          Const1,
          Add
        )
        (r, n1)

      case Con(a, b) =>
        val (r1, n1) = loop(a, n)
        val (r2, n2) = loop(b, n1)
        (r1 ++ r2, n2)

      case Alt(a, b) =>
        val (l1, n1) = mk_label(n)
        val (r1, n2) = loop(a, n1)
        val (l2, _)  = mk_label(n2)
        val (r2, n3) = loop(b, n2)
        val (l3, _)  = mk_label(n3)
        val r = List(
          Lbl(l1),
          Dup2,
          Push(n1),
          InvokeStatic(cname, mname, mtype),
          IfTrue(lmatch),
          Goto(l2)) ++
          r1 ++ (Goto(l3) :: r2)
        (r, n3)

      case Star(Star(a)) => loop(Star(a), n)

      case Star(a) =>
        val (l1, n1) = mk_label(n)
        val (r1, n2) = loop(a, n1)
        val (l2, n3) = mk_label(n2)
        val r2       = List(Lbl(l2), Goto(l1))
        val (l3, _)  = mk_label(n3)
        val r = List(
          Lbl(l1),
          Dup2,
          Push(n1),
          InvokeStatic(cname, mname, mtype),
          IfTrue(lmatch),
          Goto(l3)) ++
          r1 ++ r2
        (r, n3)
    }

    val (r, n) = loop(re, 0)
    r ++ List(Lbl(LInt(n)), Goto(lmatch))
  }

  def label_list(r: List[Repr]): List[Label] = {
    r.foldRight(Nil:List[Label])((x, y) => x match {
      case Lbl(LInt(_)) => new Label() :: y
      case _            => y
    })
  }

  def get_label (l: LId, la: List[Label] = null): Label = l match {
    case LLbl(l) => l
    case LInt(n) => la(n)
    case _       => throw new Exception()
  }

  def repr_to_code(mv: MethodVisitor, r: Repr, la: List[Label]): Unit = r match {
    case Lbl(l) => mv.visitLabel(get_label(l, la))
    case Const1 => mv.visitInsn(ICONST_1)
    case Push(n) => mv.visitIntInsn(BIPUSH, n)
    case Add => mv.visitInsn(IADD)
    case Dup2 => mv.visitInsn(DUP2)
    case Goto(l) => mv.visitJumpInsn(GOTO, get_label(l, la))
    case IfCmpNe(l) => mv.visitJumpInsn(IF_ICMPNE, get_label(l, la))
    case IfTrue(l) => mv.visitJumpInsn(IFNE, get_label(l, la))
    case InvokeVirtual(p, n, t) => mv.visitMethodInsn(INVOKEVIRTUAL, p, n, t)
    case InvokeStatic(p, n, t) => mv.visitMethodInsn(INVOKESTATIC, p, n, t)
  }

  def make(r: List[Repr]): Array[Byte] = {
    val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS)
    cw.visit(V1_5,
      ACC_PUBLIC + ACC_SUPER,
      cname,
      null,
      "java/lang/Object",
      null
    )
    cw.visitSource(cname + ".java", null)

    val mv1 = cw.visitMethod(ACC_PUBLIC, "<init>", "()V", null, null)
    mv1.visitCode()
    mv1.visitVarInsn(ALOAD, 0)
    mv1.visitMethodInsn(INVOKESPECIAL,
      "java/lang/Object",
      "<init>",
      "()V")
    mv1.visitInsn(RETURN)
    mv1.visitMaxs(0, 0)
    mv1.visitEnd()

    val mv2 = cw.visitMethod(ACC_PUBLIC + ACC_STATIC,
        mname,
        mtype,
        null,
        null)
    mv2.visitCode()

    mv2.visitVarInsn(ALOAD, 0)
    mv2.visitVarInsn(ILOAD, 1)
    mv2.visitVarInsn(ILOAD, 2)

    val la = label_list(r)
    mv2.visitLookupSwitchInsn(
      la(0),
      Range(0, la.length).toArray,
      la.toArray
    )

    r.map(x => repr_to_code(mv2, x, la))

    mv2.visitLabel(get_label(lmatch))
    mv2.visitInsn(ICONST_1)
    mv2.visitInsn(IRETURN)

    mv2.visitLabel(get_label(lmiss))
    mv2.visitInsn(ICONST_0)
    mv2.visitInsn(IRETURN)

    mv2.visitMaxs(0, 0)
    mv2.visitEnd()

    cw.visitEnd()
    cw.toByteArray
  }

  def main(args: Array[String]): Unit = {
    val re1 = Con(Con(Let('a'), Star(Let('a'))), Con(Let('b'), Star(Let('b'))))
    val re2 = Let('a')
    val re3 = Star(Let('a'))
    val re4 = Con(Con(Let('s'), Con(Con(Star(Let('a')), Star(Con(Con(Let('b'), Star(Let('a'))), Con(Let('b'), Star(Let('a')))))), Star(Let('a')))), Let('e'))
    val re5 = Con(Alt(Let('a'), Let('b')), Let('c'))
    val re6 = Con(Star(Alt(Con(Let('a'), Let('a')), Let('a'))), Let('X'))

    //val str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"

    val r = compile(re6)
    val b = make(r)

    val c = new DynamicClassLoader().define(cname, b)
    val m = c.getMethod(mname, classOf[String], classOf[Int], classOf[Int])
    val p = "(aa|a)*X".r

    for (i <- 10 to 40) {
      var str = ""
      for (_ <- 1 to i) {
        str += "a"
      }
      str += "\0"

      var time = 0.0
      for (_ <- 1 to 10) {
        val start = System.currentTimeMillis
        m.invoke(c, str, Int.box(0), Int.box(0))
        //p.findFirstIn(str)
        time += (System.currentTimeMillis - start)
      }
      println(time / 10 + ",")
    }
  }
}