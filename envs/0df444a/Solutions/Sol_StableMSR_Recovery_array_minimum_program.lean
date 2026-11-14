-- Prove2me | solution 1 for StableMSR.Recovery.array_minimum_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T02:25:38.305077+00:00
-- url     : https://prove2.me/submissions/af65aef5-a40b-4791-8546-14353627c81e

import Definitions.Def_StableMSR_Recovery_Execution
import Mathlib.Tactic
open StableMSR.Recovery
set_option maxHeartbeats 3000000
open scoped Classical
namespace StableMSR.Recovery.Compiler

/-- The data carried by a nonhalting block, separated from its program counter and work clock. -/
structure Store where
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ
  imem : ℤ → ℤ
  tapePos : ℕ
  queries : ℕ
  output : ℝ

def Store.state (s : Store) (pc work : ℕ) : MinSumFPT.State :=
  ⟨⟨pc, s.regs, s.ptrs, s.mem⟩, s.imem, s.tapePos, work, s.queries, false, s.output⟩

/-- Deterministic straight-line primitives; real literals are syntactically rational. -/
inductive Op where
  | realConst (dst : ℕ) (value : ℚ)
  | realAdd (dst a b : ℕ)
  | realSub (dst a b : ℕ)
  | realMul (dst a b : ℕ)
  | realDiv (dst a b : ℕ)
  | realLoad (dst address : ℕ)
  | realStore (address src : ℕ)
  | pointerConst (dst : ℕ) (value : ℤ)
  | pointerCopy (dst src : ℕ)
  | pointerInc (dst : ℕ)
  | pointerDec (dst : ℕ)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst src : ℕ)
  | distance (dst a b : ℕ)

noncomputable def Op.instr : Op → MinSumFPT.Instr
  | .realConst dst q => .core (.const dst (q : ℝ))
  | .realAdd dst a b => .core (.add dst a b)
  | .realSub dst a b => .core (.sub dst a b)
  | .realMul dst a b => .core (.mul dst a b)
  | .realDiv dst a b => .core (.div dst a b)
  | .realLoad dst a => .core (.load dst a)
  | .realStore a src => .core (.store a src)
  | .pointerConst dst z => .core (.pset dst z)
  | .pointerCopy dst src => .core (.pcopy dst src)
  | .pointerInc dst => .core (.pinc dst)
  | .pointerDec dst => .core (.pdec dst)
  | .pointerAdd dst a b => .pointerAdd dst a b
  | .pointerSub dst a b => .pointerSub dst a b
  | .integerLoad dst a => .integerLoad dst a
  | .integerStore a src => .integerStore a src
  | .pointerReal dst src => .pointerReal dst src
  | .distance dst a b => .dist dst a b

noncomputable def Op.eval {n : ℕ} (d : Point n → Point n → ℝ) (op : Op) (s : Store) : Store :=
  match op with
  | .realConst dst q => { s with regs := Function.update s.regs dst (q : ℝ) }
  | .realAdd dst a b => { s with regs := Function.update s.regs dst (s.regs a + s.regs b) }
  | .realSub dst a b => { s with regs := Function.update s.regs dst (s.regs a - s.regs b) }
  | .realMul dst a b => { s with regs := Function.update s.regs dst (s.regs a * s.regs b) }
  | .realDiv dst a b => { s with regs := Function.update s.regs dst (s.regs a / s.regs b) }
  | .realLoad dst a => { s with regs := Function.update s.regs dst (s.mem (s.ptrs a)) }
  | .realStore a src => { s with mem := Function.update s.mem (s.ptrs a) (s.regs src) }
  | .pointerConst dst z => { s with ptrs := Function.update s.ptrs dst z }
  | .pointerCopy dst src => { s with ptrs := Function.update s.ptrs dst (s.ptrs src) }
  | .pointerInc dst => { s with ptrs := Function.update s.ptrs dst (s.ptrs dst + 1) }
  | .pointerDec dst => { s with ptrs := Function.update s.ptrs dst (s.ptrs dst - 1) }
  | .pointerAdd dst a b => { s with ptrs := Function.update s.ptrs dst (s.ptrs a + s.ptrs b) }
  | .pointerSub dst a b => { s with ptrs := Function.update s.ptrs dst (s.ptrs a - s.ptrs b) }
  | .integerLoad dst a => { s with ptrs := Function.update s.ptrs dst (s.imem (s.ptrs a)) }
  | .integerStore a src => { s with imem := Function.update s.imem (s.ptrs a) (s.ptrs src) }
  | .pointerReal dst src => { s with regs := Function.update s.regs dst (s.ptrs src : ℝ) }
  | .distance dst a b =>
      { s with regs := Function.update s.regs dst (MinSumFPT.oracleAnswer d (s.ptrs a) (s.ptrs b)), queries := s.queries + 1 }

lemma primitive_step {n : ℕ} (P : MinSumFPT.Program) (d : Point n → Point n → ℝ)
    (ω : ℕ → ℝ) (op : Op) (s : Store) (pc w : ℕ)
    (h : P[pc]? = some op.instr) :
    MinSumFPT.step P d ω (s.state pc w) = (op.eval d s).state (pc+1) (w+1) := by
  cases op <;> simp [Op.instr, Op.eval, Store.state, MinSumFPT.step, h,
    SmaleNinth.RAMStep, List.getElem?_map, MinSumFPT.Instr.coreOf, MinSumFPT.State.next]

inductive Cond where
  | realNonpos (reg : ℕ)
  | pointerLE (a b : ℕ)

def Cond.test (c : Cond) (s : Store) : Prop :=
  match c with
  | .realNonpos r => s.regs r ≤ 0
  | .pointerLE a b => s.ptrs a ≤ s.ptrs b

noncomputable instance (c : Cond) (s : Store) : Decidable (c.test s) := Classical.propDecidable _

def Cond.instr (c : Cond) (target : ℕ) : MinSumFPT.Instr :=
  match c with
  | .realNonpos r => .core (.jle r target)
  | .pointerLE a b => .core (.pjle a b target)

def jump (target : ℕ) : MinSumFPT.Instr := .core (.pjle 0 0 target)

lemma branch_step {n : ℕ} (P : MinSumFPT.Program) (d : Point n → Point n → ℝ)
    (ω : ℕ → ℝ) (c : Cond) (s : Store) (pc w target : ℕ)
    (h : P[pc]? = some (c.instr target)) :
    MinSumFPT.step P d ω (s.state pc w) =
      s.state (if c.test s then target else pc+1) (w+1) := by
  cases c with
  | realNonpos r =>
      by_cases hc : s.regs r ≤ 0 <;>
        simp [Cond.instr, Cond.test, Store.state, MinSumFPT.step, h, hc,
          SmaleNinth.RAMStep, List.getElem?_map, MinSumFPT.Instr.coreOf]
  | pointerLE a b =>
      by_cases hc : s.ptrs a ≤ s.ptrs b <;>
        simp [Cond.instr, Cond.test, Store.state, MinSumFPT.step, h, hc,
          SmaleNinth.RAMStep, List.getElem?_map, MinSumFPT.Instr.coreOf]

lemma jump_step {n : ℕ} (P : MinSumFPT.Program) (d : Point n → Point n → ℝ)
    (ω : ℕ → ℝ) (s : Store) (pc w target : ℕ)
    (h : P[pc]? = some (jump target)) :
    MinSumFPT.step P d ω (s.state pc w) = s.state target (w+1) := by
  simp [jump, Store.state, MinSumFPT.step, h, SmaleNinth.RAMStep,
    List.getElem?_map, MinSumFPT.Instr.coreOf]

/-- A block occupies the indicated instruction interval of the ambient program. -/
def Contains (P : MinSumFPT.Program) (pc : ℕ) (code : MinSumFPT.Program) : Prop :=
  ∀ i, i < code.length → P[pc+i]? = code[i]?

lemma Contains.head {P : MinSumFPT.Program} {pc : ℕ} {i : MinSumFPT.Instr}
    {code : MinSumFPT.Program} (h : Contains P pc (i :: code)) : P[pc]? = some i := by
  simpa using h 0 (by simp)

lemma Contains.left {P A B : MinSumFPT.Program} {pc : ℕ}
    (h : Contains P pc (A ++ B)) : Contains P pc A := by
  intro i hi
  rw [h i (by simp only [List.length_append]; omega)]
  exact List.getElem?_append_left hi

lemma Contains.right {P A B : MinSumFPT.Program} {pc : ℕ}
    (h : Contains P pc (A ++ B)) : Contains P (pc+A.length) B := by
  intro i hi
  rw [Nat.add_assoc, h (A.length+i) (by simp only [List.length_append]; omega)]
  rw [List.getElem?_append_right (by omega)]
  simp

lemma Contains.tail {P : MinSumFPT.Program} {pc : ℕ} {i : MinSumFPT.Instr}
    {code : MinSumFPT.Program} (h : Contains P pc (i :: code)) : Contains P (pc+1) code := by
  exact h.right (A := [i])

lemma contains_context (pre code suffix : MinSumFPT.Program) :
    Contains (pre ++ code ++ suffix) pre.length code := by
  intro i hi
  rw [List.append_assoc]
  simp only [List.getElem?_append_right (by omega : pre.length ≤ pre.length+i),
    Nat.add_sub_cancel_left]
  exact List.getElem?_append_left hi

/-- Structured deterministic blocks. While loops carry finite execution proofs
at use sites; compiling a block does not assume or assert termination. -/
inductive Cmd where
  | skip
  | atom (op : Op)
  | seq (first second : Cmd)
  | ite (c : Cond) (yes no : Cmd)
  | whileDo (c : Cond) (body : Cmd)

def Cmd.size : Cmd → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq a b => a.size + b.size
  | .ite _ yes no => 1 + no.size + 1 + yes.size
  | .whileDo _ body => 2 + body.size + 1

/-- Absolute branch destinations are computed from the block's actual location. -/
noncomputable def compileAt (pc : ℕ) : Cmd → MinSumFPT.Program
  | .skip => []
  | .atom op => [op.instr]
  | .seq a b => compileAt pc a ++ compileAt (pc+a.size) b
  | .ite c yes no => c.instr (pc+1+no.size+1) ::
      (compileAt (pc+1) no ++ jump (pc+1+no.size+1+yes.size) ::
        compileAt (pc+1+no.size+1) yes)
  | .whileDo c body => c.instr (pc+2) :: jump (pc+2+body.size+1) ::
      (compileAt (pc+2) body ++ [jump pc])

@[simp] lemma compileAt_length (pc : ℕ) (cmd : Cmd) : (compileAt pc cmd).length = cmd.size := by
  induction cmd generalizing pc <;> simp_all [compileAt, Cmd.size] <;> omega

/-- Bounded structured semantics with exact machine instruction charges.
A taken conditional costs one test; a false conditional also executes a jump.
Each successful while iteration has two control steps; its final failed test
and exit jump cost two more. -/
inductive Executes {n : ℕ} (d : Point n → Point n → ℝ) : Cmd → Store → Store → ℕ → Prop
  | skip (s : Store) : Executes d .skip s s 0
  | atom (op : Op) (s : Store) : Executes d (.atom op) s (op.eval d s) 1
  | seq {a b : Cmd} {s t u : Store} {i j : ℕ} :
      Executes d a s t i → Executes d b t u j → Executes d (.seq a b) s u (i+j)
  | ite_true {c : Cond} {yes no : Cmd} {s t : Store} {i : ℕ} :
      c.test s → Executes d yes s t i → Executes d (.ite c yes no) s t (1+i)
  | ite_false {c : Cond} {yes no : Cmd} {s t : Store} {i : ℕ} :
      ¬ c.test s → Executes d no s t i → Executes d (.ite c yes no) s t (1+i+1)
  | while_false {c : Cond} {body : Cmd} {s : Store} :
      ¬ c.test s → Executes d (.whileDo c body) s s 2
  | while_true {c : Cond} {body : Cmd} {s t u : Store} {i j : ℕ} :
      c.test s → Executes d body s t i → Executes d (.whileDo c body) t u j →
      Executes d (.whileDo c body) s u (1+i+1+j)

lemma iterate_compose {α : Type*} {f : α → α} {s t u : α} {a b : ℕ}
    (ha : f^[a] s = t) (hb : f^[b] t = u) : f^[a+b] s = u := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, ha, hb]

/-- Every finite structured derivation is simulated by the concrete embedded
instruction list, with exactly its stated step and charged-work count. -/
theorem compileAt_simulates {n : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {s t : Store} {cost : ℕ} (h : Executes d cmd s t cost) :
    ∀ (P : MinSumFPT.Program) (ω : ℕ → ℝ) (pc w : ℕ),
      Contains P pc (compileAt pc cmd) →
      (MinSumFPT.step P d ω)^[cost] (s.state pc w) =
        t.state (pc+cmd.size) (w+cost) := by
  induction h with
  | skip s =>
      intro P ω pc w hc
      simp [Cmd.size]
  | atom op s =>
      intro P ω pc w hc
      simpa [Cmd.size] using primitive_step P d ω op s pc w hc.head
  | @seq a b s t u i j ha hb iha ihb =>
      intro P ω pc w hc
      have hl : Contains P pc (compileAt pc a) := hc.left
      have hr : Contains P (pc+a.size) (compileAt (pc+a.size) b) := by
        simpa only [compileAt_length] using hc.right
      have h₁ := iha P ω pc w hl
      have h₂ := ihb P ω (pc+a.size) (w+i) hr
      simpa only [Cmd.size, Nat.add_assoc] using iterate_compose h₁ h₂
  | @ite_true c yes no s t i ht he ih =>
      intro P ω pc w hc
      have hn : Contains P (pc+1) (compileAt (pc+1) no ++
          jump (pc+1+no.size+1+yes.size) :: compileAt (pc+1+no.size+1) yes) := hc.tail
      have hj : Contains P (pc+1+no.size)
          (jump (pc+1+no.size+1+yes.size) :: compileAt (pc+1+no.size+1) yes) := by
        simpa only [compileAt_length] using hn.right
      have hy := hj.tail
      have h₁ : (MinSumFPT.step P d ω)^[1] (s.state pc w) =
          s.state (pc+1+no.size+1) (w+1) := by
        simpa only [Function.iterate_one, if_pos ht] using
          branch_step P d ω c s pc w (pc+1+no.size+1) hc.head
      have h₂ := ih P ω (pc+1+no.size+1) (w+1) hy
      simpa only [Cmd.size, Nat.add_assoc] using iterate_compose h₁ h₂
  | @ite_false c yes no s t i ht he ih =>
      intro P ω pc w hc
      have hn : Contains P (pc+1) (compileAt (pc+1) no ++
          jump (pc+1+no.size+1+yes.size) :: compileAt (pc+1+no.size+1) yes) := hc.tail
      have hj : Contains P (pc+1+no.size)
          (jump (pc+1+no.size+1+yes.size) :: compileAt (pc+1+no.size+1) yes) := by
        simpa only [compileAt_length] using hn.right
      have h₁ : (MinSumFPT.step P d ω)^[1] (s.state pc w) = s.state (pc+1) (w+1) := by
        simpa only [Function.iterate_one, if_neg ht] using
          branch_step P d ω c s pc w (pc+1+no.size+1) hc.head
      have h₂ := ih P ω (pc+1) (w+1) hn.left
      have h₃ : (MinSumFPT.step P d ω)^[1] (t.state (pc+1+no.size) (w+1+i)) =
          t.state (pc+1+no.size+1+yes.size) (w+1+i+1) := by
        simpa only [Function.iterate_one] using jump_step P d ω t
          (pc+1+no.size) (w+1+i) (pc+1+no.size+1+yes.size) hj.head
      simpa only [Cmd.size, Nat.add_assoc] using
        iterate_compose (iterate_compose h₁ h₂) h₃
  | @while_false c body s ht =>
      intro P ω pc w hc
      have hj : Contains P (pc+1) (jump (pc+2+body.size+1) ::
          (compileAt (pc+2) body ++ [jump pc])) := hc.tail
      have h₁ : (MinSumFPT.step P d ω)^[1] (s.state pc w) = s.state (pc+1) (w+1) := by
        simpa only [Function.iterate_one, if_neg ht] using
          branch_step P d ω c s pc w (pc+2) hc.head
      have h₂ : (MinSumFPT.step P d ω)^[1] (s.state (pc+1) (w+1)) =
          s.state (pc+2+body.size+1) (w+1+1) := by
        simpa only [Function.iterate_one] using
          jump_step P d ω s (pc+1) (w+1) (pc+2+body.size+1) hj.head
      simpa only [Cmd.size, Nat.add_assoc] using iterate_compose h₁ h₂
  | @while_true c body s t u i j ht hb hw ihb ihw =>
      intro P ω pc w hc
      have htail : Contains P (pc+2) (compileAt (pc+2) body ++ [jump pc]) := by
        simpa only [Nat.add_assoc] using hc.tail.tail
      have hback : Contains P (pc+2+body.size) [jump pc] := by
        simpa only [compileAt_length] using htail.right
      have h₁ : (MinSumFPT.step P d ω)^[1] (s.state pc w) = s.state (pc+2) (w+1) := by
        simpa only [Function.iterate_one, if_pos ht] using
          branch_step P d ω c s pc w (pc+2) hc.head
      have h₂ := ihb P ω (pc+2) (w+1) htail.left
      have h₃ : (MinSumFPT.step P d ω)^[1] (t.state (pc+2+body.size) (w+1+i)) =
          t.state pc (w+1+i+1) := by
        simpa only [Function.iterate_one] using
          jump_step P d ω t (pc+2+body.size) (w+1+i) pc hback.head
      have h₄ := ihw P ω pc (w+1+i+1) hc
      simpa only [Nat.add_assoc] using
        iterate_compose (iterate_compose (iterate_compose h₁ h₂) h₃) h₄

/-- Every emitted instruction is admissible and excludes random-tape reads. -/
def SafeInstr (i : MinSumFPT.Instr) : Prop :=
  ((∀ dst c, i = .core (.const dst c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject) ∧
    match i with | .unif _ | .uniformIndex _ _ => False | _ => True

lemma Op.safe (op : Op) : SafeInstr op.instr := by
  cases op <;> simp [SafeInstr, Op.instr]

lemma Cond.safe (c : Cond) (target : ℕ) : SafeInstr (c.instr target) := by
  cases c <;> simp [SafeInstr, Cond.instr]

lemma jump_safe (target : ℕ) : SafeInstr (jump target) := by simp [SafeInstr, jump]

lemma compileAt_safe (pc : ℕ) (cmd : Cmd) :
    ∀ i ∈ compileAt pc cmd, SafeInstr i := by
  induction cmd generalizing pc with
  | skip => simp [compileAt]
  | atom op => simpa only [compileAt, List.mem_singleton, forall_eq] using op.safe
  | seq a b iha ihb =>
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact iha pc i h
      · exact ihb (pc+a.size) i h
  | ite c yes no ihy ihn =>
      intro i hi
      simp only [compileAt, List.mem_cons, List.mem_append] at hi
      rcases hi with rfl | hn | rfl | hy
      · exact c.safe _
      · exact ihn _ i hn
      · exact jump_safe _
      · exact ihy _ i hy
  | whileDo c body ih =>
      intro i hi
      simp only [compileAt, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | hb | rfl
      · exact c.safe _
      · exact jump_safe _
      · exact ih _ i hb
      · exact jump_safe _

lemma compileAt_deterministic (pc : ℕ) (cmd : Cmd) :
    DeterministicProgram (compileAt pc cmd) := by
  constructor
  · intro i hi
    exact (compileAt_safe pc cmd i hi).1
  · intro i hi
    exact (compileAt_safe pc cmd i hi).2

/-- A bounded finite execution, with no assumption that arbitrary loops terminate. -/
def BoundedExec {n : ℕ} (d : Point n → Point n → ℝ) (cmd : Cmd)
    (s t : Store) (budget : ℕ) : Prop := ∃ cost ≤ budget, Executes d cmd s t cost

/-- A finite loop invariant chain yields the explicit body-plus-control budget.
Each body costs at most B; each iteration costs two additional instructions,
and the failed guard plus exit jump costs two. -/
theorem bounded_while {n : ℕ} (d : Point n → Point n → ℝ) (c : Cond) (body : Cmd)
    (q B : ℕ) (states : ℕ → Store)
    (htest : ∀ i < q, c.test (states i))
    (hbody : ∀ i < q, BoundedExec d body (states i) (states (i+1)) B)
    (hexit : ¬ c.test (states q)) :
    BoundedExec d (.whileDo c body) (states 0) (states q) (q*(B+2)+2) := by
  induction q generalizing states with
  | zero =>
      exact ⟨2, by omega, Executes.while_false hexit⟩
  | succ q ih =>
      obtain ⟨i, hi, hrun⟩ := hbody 0 (by omega)
      have ht : ∀ j < q, c.test ((fun a => states (a+1)) j) := by
        intro j hj
        exact htest (j+1) (by omega)
      have hb : ∀ j < q, BoundedExec d body ((fun a => states (a+1)) j)
          ((fun a => states (a+1)) (j+1)) B := by
        intro j hj
        exact hbody (j+1) (by omega)
      obtain ⟨r, hr, hrest⟩ := ih (fun a => states (a+1)) ht hb hexit
      refine ⟨1+i+1+r, ?_, Executes.while_true (htest 0 (by omega)) hrun hrest⟩
      nlinarith

/-- Contextual bounded simulation also bounds the interpreter's charged work. -/
theorem bounded_simulates {n : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {s t : Store} {budget : ℕ} (h : BoundedExec d cmd s t budget)
    (P : MinSumFPT.Program) (ω : ℕ → ℝ) (pc w : ℕ)
    (hc : Contains P pc (compileAt pc cmd)) :
    ∃ steps ≤ budget, (MinSumFPT.step P d ω)^[steps] (s.state pc w) =
      t.state (pc+cmd.size) (w+steps) := by
  obtain ⟨steps, hs, he⟩ := h
  exact ⟨steps, hs, compileAt_simulates he P ω pc w hc⟩

/-- Turn a terminating block into a complete program with one charged halt. -/
noncomputable def compile (cmd : Cmd) (result : ℕ := 0) : MinSumFPT.Program :=
  compileAt 0 cmd ++ [.halt result]

lemma compile_deterministic (cmd : Cmd) (result : ℕ) : DeterministicProgram (compile cmd result) := by
  have hs : ∀ i ∈ compile cmd result, SafeInstr i := by
    intro i hi
    rcases List.mem_append.mp hi with hb | hh
    · exact compileAt_safe 0 cmd i hb
    · have hi' : i = .halt result := List.mem_singleton.mp hh
      simp [hi', SafeInstr]
  exact ⟨fun i hi => (hs i hi).1, fun i hi => (hs i hi).2⟩

def Store.haltedState (s : Store) (pc w result : ℕ) : MinSumFPT.State :=
  { s.state pc w with halted := true, output := s.regs result }

lemma halt_step {n : ℕ} (P : MinSumFPT.Program) (d : Point n → Point n → ℝ)
    (ω : ℕ → ℝ) (s : Store) (pc w result : ℕ) (h : P[pc]? = some (.halt result)) :
    MinSumFPT.step P d ω (s.state pc w) = s.haltedState pc (w+1) result := by
  simp [MinSumFPT.step, Store.state, Store.haltedState, h]

/-- Closed-program execution, including the actual final halt instruction. -/
theorem compile_halts {n : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {s t : Store} {cost : ℕ} (h : Executes d cmd s t cost)
    (ω : ℕ → ℝ) (w result : ℕ) :
    (MinSumFPT.step (compile cmd result) d ω)^[cost+1] (s.state 0 w) =
      t.haltedState cmd.size (w+cost+1) result := by
  have hc : Contains (compile cmd result) 0 (compileAt 0 cmd) := by
    simpa only [compile, List.nil_append, List.length_nil] using
      contains_context [] (compileAt 0 cmd) [.halt result]
  have he := compileAt_simulates h (compile cmd result) ω 0 w hc
  simp only [Nat.zero_add] at he
  have hf : (compile cmd result)[cmd.size]? = some (.halt result) := by
    unfold compile
    rw [List.getElem?_append_right (by simp)]
    simp
  have hh : (MinSumFPT.step (compile cmd result) d ω)^[1]
      (t.state cmd.size (w+cost)) = t.haltedState cmd.size (w+cost+1) result := by
    simpa only [Function.iterate_one] using
      halt_step (compile cmd result) d ω t cmd.size (w+cost) result hf
  simpa only [Nat.zero_add] using iterate_compose he hh

/-- The canonical wrapper's input store, with its two scalar inputs fixed to zero. -/
def initialStore (n k : ℕ) : Store :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0,
    fun a => if a = 0 then (n : ℤ) else if a = 1 then (k : ℤ) else 0, 0, 0, 0⟩

lemma initialStore_state (n k : ℕ) : (initialStore n k).state 0 0 =
    MinSumFPT.initState n k 0 0 := by
  simp [initialStore, Store.state, MinSumFPT.initState]

/-- A concrete compiler bridge from a structured algorithm proof to execute. -/
theorem execute_compile {n k : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {t : Store} {cost : ℕ}
    (h : Executes d cmd (initialStore n k) t cost) (result : ℕ) :
    execute (compile cmd result) n k d (cost+1) =
      t.haltedState cmd.size (cost+1) result := by
  have he := compile_halts h (fun _ => 0) 0 result
  rw [initialStore_state] at he
  simpa only [execute, MinSumFPT.run, Nat.zero_add] using he

/-- A compiled block may be relocated after any prefix and before any suffix;
all internal jump destinations and charged execution counts remain correct. -/
theorem relocated_simulation {n : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {s t : Store} {cost : ℕ} (h : Executes d cmd s t cost)
    (pre suffix : MinSumFPT.Program) (ω : ℕ → ℝ) (w : ℕ) :
    (MinSumFPT.step (pre ++ compileAt pre.length cmd ++ suffix) d ω)^[cost]
        (s.state pre.length w) = t.state (pre.length+cmd.size) (w+cost) := by
  exact compileAt_simulates h _ ω pre.length w
    (contains_context pre (compileAt pre.length cmd) suffix)

/-- An upper bound on structured costs becomes a bound on actual execution and
charged work, with only the single final halt added. -/
theorem execute_compile_bounded {n k : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {t : Store} {budget : ℕ}
    (h : BoundedExec d cmd (initialStore n k) t budget) (result : ℕ) :
    ∃ steps ≤ budget+1,
      let s := execute (compile cmd result) n k d steps
      s = t.haltedState cmd.size steps result ∧
      s.halted = true ∧ s.work ≤ budget+1 ∧ s.imem = t.imem := by
  obtain ⟨cost, hcost, he⟩ := h
  refine ⟨cost+1, by omega, ?_⟩
  rw [execute_compile he result]
  exact ⟨rfl, rfl, by change cost+1 ≤ budget+1; omega, rfl⟩

end StableMSR.Recovery.Compiler

namespace StableMSR.Recovery.Compiler.ArgminNumeric
open scoped Classical

/-- Index of the last minimum in the nonempty prefix `0,...,i`. -/
noncomputable def prefixArgmin (f : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | i+1 => if f (i+1) ≤ f (prefixArgmin f i) then i+1 else prefixArgmin f i

@[simp] theorem prefixArgmin_zero (f : ℕ → ℝ) : prefixArgmin f 0 = 0 := rfl

theorem prefixArgmin_succ (f : ℕ → ℝ) (i : ℕ) :
    prefixArgmin f (i+1) =
      if f (i+1) ≤ f (prefixArgmin f i) then i+1 else prefixArgmin f i := rfl

/-- The selected address is always one of the inspected entries. -/
theorem prefixArgmin_le (f : ℕ → ℝ) (i : ℕ) : prefixArgmin f i ≤ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [prefixArgmin_succ]
    split_ifs <;> omega

/-- The maintained value is no larger than any inspected array entry. -/
theorem prefixArgmin_min (f : ℕ → ℝ) (i j : ℕ) (hj : j ≤ i) :
    f (prefixArgmin f i) ≤ f j := by
  induction i with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    simp
  | succ i ih =>
    rw [prefixArgmin_succ]
    split_ifs with hnew
    · by_cases hji : j ≤ i
      · exact hnew.trans (ih hji)
      · have hjs : j = i+1 := by omega
        subst j
        exact le_rfl
    · by_cases hji : j ≤ i
      · exact ih hji
      · have hjs : j = i+1 := by omega
        subst j
        exact (lt_of_not_ge hnew).le

/-- Updating on nonpositive differences implements deterministic last-tie selection. -/
theorem prefixArgmin_last_tie (f : ℕ → ℝ) (i j : ℕ) (hj : j ≤ i)
    (heq : f j = f (prefixArgmin f i)) : j ≤ prefixArgmin f i := by
  induction i with
  | zero => simpa using hj
  | succ i ih =>
    rw [prefixArgmin_succ] at heq ⊢
    split_ifs at heq ⊢ with hnew
    · exact hj
    · have hji : j ≤ i := by
        by_contra hn
        have hjs : j = i+1 := by omega
        subst j
        exact hnew heq.le
      exact ih hji heq

/-- A complete functional specification for a nonempty finite array. -/
theorem nonempty_array_argmin (f : ℕ → ℝ) (length : ℕ) (hpos : 0 < length) :
    prefixArgmin f (length-1) < length ∧
    (∀ j < length, f (prefixArgmin f (length-1)) ≤ f j) ∧
    (∀ j < length, f j = f (prefixArgmin f (length-1)) →
      j ≤ prefixArgmin f (length-1)) := by
  refine ⟨lt_of_le_of_lt (prefixArgmin_le f _) (by omega),?_,?_⟩
  · intro j hj
    exact prefixArgmin_min f _ j (by omega)
  · intro j hj heq
    exact prefixArgmin_last_tie f _ j (by omega) heq

/-- Appending more inspected entries cannot worsen the selected value. -/
theorem prefixArgmin_value_antitone (f : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) :
    f (prefixArgmin f j) ≤ f (prefixArgmin f i) :=
  prefixArgmin_min f j _ ((prefixArgmin_le f i).trans hij)

/-- A known global minimum occurring in the scanned prefix is recovered exactly. -/
theorem prefixArgmin_eq_minimum (f : ℕ → ℝ) (i j : ℕ) (hj : j ≤ i)
    (hmin : ∀ k ≤ i, f j ≤ f k) : f (prefixArgmin f i) = f j := by
  exact le_antisymm (prefixArgmin_min f i j hj) (hmin _ (prefixArgmin_le f i))
end StableMSR.Recovery.Compiler.ArgminNumeric
open StableMSR.Recovery.Compiler
namespace StableMSR.Recovery.Compiler.Argmin
/-- Pointers 0,1 initially give first and last array addresses; pointer 2 returns a minimizer. -/
def body : Cmd := .seq (.atom (.realLoad 0 0))
  (.seq (.atom (.realLoad 1 2))
    (.seq (.atom (.realSub 2 0 1))
      (.seq (.ite (.realNonpos 2) (.atom (.pointerCopy 2 0)) .skip)
        (.atom (.pointerInc 0)))))
def loop : Cmd := .whileDo (.pointerLE 0 1) body
def setup : Cmd := .seq (.atom (.pointerCopy 2 0)) (.atom (.pointerInc 0))
def block : Cmd := .seq setup (.seq loop (.atom (.realLoad 0 2)))
noncomputable def step {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) : Store :=
  let a := (Op.realLoad 0 0).eval d s
  let b := (Op.realLoad 1 2).eval d a
  let c := (Op.realSub 2 0 1).eval d b
  let e := if (Cond.realNonpos 2).test c then (Op.pointerCopy 2 0).eval d c else c
  (Op.pointerInc 0).eval d e
noncomputable def initial {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) : Store :=
  (Op.pointerInc 0).eval d ((Op.pointerCopy 2 0).eval d s)
lemma body_exec {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    Executes d body s (step d s) 6 := by
  unfold body step
  dsimp only
  refine Executes.seq (i := 1) (j := 5) (Executes.atom _ _)
    (Executes.seq (i := 1) (j := 4) (Executes.atom _ _)
    (Executes.seq (i := 1) (j := 3) (Executes.atom _ _)
    (Executes.seq (i := 2) (j := 1) ?_ (Executes.atom _ _))))
  split_ifs with h
  · exact Executes.ite_true h (Executes.atom _ _)
  · exact Executes.ite_false h (Executes.skip _)
lemma setup_exec {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    Executes d setup s (initial d s) 2 :=
  Executes.seq (Executes.atom _ _) (Executes.atom _ _)
lemma step_ptr0 {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    (step d s).ptrs 0 = s.ptrs 0 + 1 := by
  simp [step,Cond.test,Op.eval]; split_ifs <;> simp
lemma step_ptr1 {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    (step d s).ptrs 1 = s.ptrs 1 := by
  simp [step,Cond.test,Op.eval]; split_ifs <;> simp
lemma step_ptr2 {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    (step d s).ptrs 2 = if s.mem (s.ptrs 0) ≤ s.mem (s.ptrs 2) then s.ptrs 0 else s.ptrs 2 := by
  simp [step,Cond.test,Op.eval,sub_nonpos]; split_ifs <;> simp_all
lemma step_mem {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    (step d s).mem = s.mem := by
  simp [step,Cond.test,Op.eval]; split_ifs <;> rfl
lemma step_imem {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    (step d s).imem = s.imem := by
  simp [step,Cond.test,Op.eval]; split_ifs <;> rfl
lemma step_queries {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    (step d s).queries = s.queries := by
  simp [step,Cond.test,Op.eval]; split_ifs <;> rfl
lemma step_tapePos {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    (step d s).tapePos = s.tapePos := by
  simp [step,Cond.test,Op.eval]; split_ifs <;> rfl
lemma loop_exec {n : ℕ} (d : Point n → Point n → ℝ) (q : ℕ) (s : Store)
    (hbound : s.ptrs 1 = s.ptrs 0 + (q : ℤ) - 1) :
    Executes d loop s ((step d)^[q] s) (8*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test]
    omega
  | succ q ih =>
    have htest : (Cond.pointerLE 0 1).test s := by
      simp only [Cond.test]; omega
    have hb : (step d s).ptrs 1 = (step d s).ptrs 0 + (q : ℤ) - 1 := by
      rw [step_ptr0,step_ptr1]; omega
    have hr := Executes.while_true htest (body_exec d s) (ih (step d s) hb)
    simpa only [loop,Function.iterate_succ_apply,show 1+6+1+(8*q+2) = 8*(q+1)+2 by omega] using hr
noncomputable def states {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) (q : ℕ) : Store :=
  (step d)^[q] (initial d s)
lemma states_invariant {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) (q : ℕ) :
    (states d s q).ptrs 0 = s.ptrs 0 + (q+1 : ℕ) ∧
    (states d s q).ptrs 1 = s.ptrs 1 ∧
    (states d s q).ptrs 2 = s.ptrs 0 + ArgminNumeric.prefixArgmin (fun i => s.mem (s.ptrs 0 + i)) q ∧
    (states d s q).mem = s.mem ∧ (states d s q).imem = s.imem ∧
    (states d s q).queries = s.queries ∧ (states d s q).tapePos = s.tapePos := by
  induction q with
  | zero => simp [states,initial,Op.eval]
  | succ q ih =>
    have hs : states d s (q+1) = step d (states d s q) := by
      simp [states,Function.iterate_succ_apply']
    rw [hs,step_ptr0,step_ptr1,step_ptr2,step_mem,step_imem,step_queries,step_tapePos]
    rw [ih.1,ih.2.1,ih.2.2.1,ih.2.2.2.1]
    refine ⟨by push_cast; omega,rfl,?_,rfl,ih.2.2.2.2⟩
    rw [ArgminNumeric.prefixArgmin_succ]
    split_ifs <;> simp_all
/-- The concrete block terminates in exactly 8q+5 steps on q+1 entries. -/
theorem block_correct {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) (q : ℕ)
    (hbound : s.ptrs 1 = s.ptrs 0 + (q : ℤ)) :
    ∃ t : Store, Executes d block s t (8*q+5) ∧
      (∃ j ≤ q, t.ptrs 2 = s.ptrs 0 + (j : ℤ) ∧
        t.regs 0 = s.mem (s.ptrs 0 + j) ∧
        ∀ i ≤ q, t.regs 0 ≤ s.mem (s.ptrs 0 + (i : ℤ))) ∧
      t.mem = s.mem ∧ t.imem = s.imem ∧ t.queries = s.queries ∧ t.tapePos = s.tapePos := by
  let t := (Op.realLoad 0 2).eval d (states d s q)
  have hi : (initial d s).ptrs 1 = (initial d s).ptrs 0 + (q : ℤ) - 1 := by
    simp [initial,Op.eval]; omega
  have hr := Executes.seq (setup_exec d s)
    (Executes.seq (loop_exec d q (initial d s) hi) (Executes.atom (Op.realLoad 0 2) (states d s q)))
  have hinv := states_invariant d s q
  refine ⟨t,?_,?_,?_,?_,?_,?_⟩
  · convert hr using 1 <;> first | rfl | omega
  · refine ⟨ArgminNumeric.prefixArgmin (fun i => s.mem (s.ptrs 0 + i)) q,
      ArgminNumeric.prefixArgmin_le _ _,?_,?_,?_⟩
    · exact hinv.2.2.1
    · simpa [t,Op.eval,hinv.2.2.2.1,hinv.2.2.1]
    · intro i hi
      simpa [t,Op.eval,hinv.2.2.2.1,hinv.2.2.1] using
        ArgminNumeric.prefixArgmin_min (fun i => s.mem (s.ptrs 0 + i)) q i hi
  · exact hinv.2.2.2.1
  · exact hinv.2.2.2.2.1
  · exact hinv.2.2.2.2.2.1
  · exact hinv.2.2.2.2.2.2
/-- One fixed deterministic program scans any nonempty real array in linear charged time.
Its initial memory and all integer memory are preserved; pointer 2 identifies the minimizer. -/
theorem compiled_argmin :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
      ∀ (n : ℕ) (d : Point n → Point n → ℝ) (s : Store) (q : ℕ),
        s.ptrs 1 = s.ptrs 0 + (q : ℤ) → ∀ (ω : ℕ → ℝ) (w : ℕ),
        let result := (MinSumFPT.step P d ω)^[8*q+6] (s.state 0 w)
        result.halted = true ∧ result.work = w+8*q+6 ∧
        (∃ j ≤ q, result.cfg.ptrs 2 = s.ptrs 0 + (j : ℤ) ∧
          result.output = s.mem (s.ptrs 0 + j) ∧
          ∀ i ≤ q, result.output ≤ s.mem (s.ptrs 0 + (i : ℤ))) ∧
        result.cfg.mem = s.mem ∧ result.imem = s.imem ∧
        result.queries = s.queries ∧ result.tapePos = s.tapePos := by
  refine ⟨compile block 0,compile_deterministic block 0,?_⟩
  intro n d s q hbound ω w
  obtain ⟨t,hex,hmin,hmem,himem,hqueries,htape⟩ := block_correct d s q hbound
  have he := compile_halts hex ω w 0
  simp only [show 8*q+5+1 = 8*q+6 by omega] at he
  dsimp only
  rw [he]
  change true = true ∧ w+(8*q+5)+1 = w+8*q+6 ∧
    (∃ j ≤ q, t.ptrs 2 = s.ptrs 0 + (j : ℤ) ∧
      t.regs 0 = s.mem (s.ptrs 0+j) ∧ ∀ i ≤ q, t.regs 0 ≤ s.mem (s.ptrs 0+(i:ℤ))) ∧
    t.mem = s.mem ∧ t.imem = s.imem ∧ t.queries = s.queries ∧ t.tapePos = s.tapePos
  exact ⟨rfl,by omega,hmin,hmem,himem,hqueries,htape⟩
end StableMSR.Recovery.Compiler.Argmin
open StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.Argmin
/-- Standalone machine-state specification, requiring no external compiler interface. -/
theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
      ∀ (n : ℕ) (d : Point n → Point n → ℝ) (s : MinSumFPT.State) (q : ℕ),
        s.cfg.pc = 0 → s.halted = false → s.cfg.ptrs 1 = s.cfg.ptrs 0 + (q : ℤ) →
        ∀ ω : ℕ → ℝ,
        let result := (MinSumFPT.step P d ω)^[8*q+6] s
        result.halted = true ∧ result.work = s.work+8*q+6 ∧
        (∃ j ≤ q, result.cfg.ptrs 2 = s.cfg.ptrs 0 + (j : ℤ) ∧
          result.output = s.cfg.mem (s.cfg.ptrs 0 + j) ∧
          ∀ i ≤ q, result.output ≤ s.cfg.mem (s.cfg.ptrs 0 + (i : ℤ))) ∧
        result.cfg.mem = s.cfg.mem ∧ result.imem = s.imem ∧
        result.queries = s.queries ∧ result.tapePos = s.tapePos := by
  obtain ⟨P,hP,hscan⟩ := compiled_argmin
  refine ⟨P,hP,?_⟩
  intro n d s q hpc hhalt hbound ω
  let st : Store := ⟨s.cfg.regs,s.cfg.ptrs,s.cfg.mem,s.imem,s.tapePos,s.queries,s.output⟩
  have he : st.state 0 s.work = s := by
    cases s with
    | mk cfg imem tp work queries halted output =>
      cases cfg
      simp_all [st,Store.state]
  have h := hscan n d st q hbound ω s.work
  rw [he] at h
  exact h
