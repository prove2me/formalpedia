-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.compiler_execution_exact
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T19:35:58.793181+00:00
-- url     : https://prove2.me/submissions/8b864d7a-bef6-4e96-a837-536c1d77fdc8

import Definitions.Def_StableMSR_StructuredCompiler
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
open StableMSR.Recovery
namespace StableMSR.Recovery.Compiler
lemma primitive_step {n : ℕ} (P : MinSumFPT.Program) (d : Point n → Point n → ℝ)
    (ω : ℕ → ℝ) (op : Op) (s : Store) (pc w : ℕ)
    (h : P[pc]? = some op.instr) :
    MinSumFPT.step P d ω (s.state pc w) = (op.eval d s).state (pc+1) (w+1) := by
  cases op <;> simp [Op.instr, Op.eval, Store.state, MinSumFPT.step, h,
    SmaleNinth.RAMStep, List.getElem?_map, MinSumFPT.Instr.coreOf, MinSumFPT.State.next]


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

/- A block occupies the indicated instruction interval of the ambient program. -/

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

/- Structured deterministic blocks. While loops carry finite execution proofs
at use sites; compiling a block does not assume or assert termination. -/

@[simp] lemma compileAt_length (pc : ℕ) (cmd : Cmd) : (compileAt pc cmd).length = cmd.size := by
  induction cmd generalizing pc <;> simp_all [compileAt, Cmd.size] <;> omega

/- Bounded structured semantics with exact machine instruction charges.
A taken conditional costs one test; a false conditional also executes a jump.
Each successful while iteration has two control steps; its final failed test
and exit jump cost two more. -/

lemma iterate_compose {α : Type*} {f : α → α} {s t u : α} {a b : ℕ}
    (ha : f^[a] s = t) (hb : f^[b] t = u) : f^[a+b] s = u := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, ha, hb]

/- Every finite structured derivation is simulated by the concrete embedded
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

/- Every emitted instruction is admissible and excludes random-tape reads. -/

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

/- A bounded finite execution, with no assumption that arbitrary loops terminate. -/

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

/- Contextual bounded simulation also bounds the interpreter's charged work. -/

theorem bounded_simulates {n : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {s t : Store} {budget : ℕ} (h : BoundedExec d cmd s t budget)
    (P : MinSumFPT.Program) (ω : ℕ → ℝ) (pc w : ℕ)
    (hc : Contains P pc (compileAt pc cmd)) :
    ∃ steps ≤ budget, (MinSumFPT.step P d ω)^[steps] (s.state pc w) =
      t.state (pc+cmd.size) (w+steps) := by
  obtain ⟨steps, hs, he⟩ := h
  exact ⟨steps, hs, compileAt_simulates he P ω pc w hc⟩

/- Turn a terminating block into a complete program with one charged halt. -/

lemma compile_deterministic (cmd : Cmd) (result : ℕ) : DeterministicProgram (compile cmd result) := by
  have hs : ∀ i ∈ compile cmd result, SafeInstr i := by
    intro i hi
    rcases List.mem_append.mp hi with hb | hh
    · exact compileAt_safe 0 cmd i hb
    · have hi' : i = .halt result := List.mem_singleton.mp hh
      simp [hi', SafeInstr]
  exact ⟨fun i hi => (hs i hi).1, fun i hi => (hs i hi).2⟩


lemma halt_step {n : ℕ} (P : MinSumFPT.Program) (d : Point n → Point n → ℝ)
    (ω : ℕ → ℝ) (s : Store) (pc w result : ℕ) (h : P[pc]? = some (.halt result)) :
    MinSumFPT.step P d ω (s.state pc w) = s.haltedState pc (w+1) result := by
  simp [MinSumFPT.step, Store.state, Store.haltedState, h]

/- Closed-program execution, including the actual final halt instruction. -/

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

/- The canonical wrapper's input store, with its two scalar inputs fixed to zero. -/

lemma initialStore_state (n k : ℕ) : (initialStore n k).state 0 0 =
    MinSumFPT.initState n k 0 0 := by
  simp [initialStore, Store.state, MinSumFPT.initState]

/- A concrete compiler bridge from a structured algorithm proof to execute. -/

theorem execute_compile {n k : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {t : Store} {cost : ℕ}
    (h : Executes d cmd (initialStore n k) t cost) (result : ℕ) :
    execute (compile cmd result) n k d (cost+1) =
      t.haltedState cmd.size (cost+1) result := by
  have he := compile_halts h (fun _ => 0) 0 result
  rw [initialStore_state] at he
  simpa only [execute, MinSumFPT.run, Nat.zero_add] using he

/- A compiled block may be relocated after any prefix and before any suffix;
all internal jump destinations and charged execution counts remain correct. -/

theorem relocated_simulation {n : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {s t : Store} {cost : ℕ} (h : Executes d cmd s t cost)
    (pre suffix : MinSumFPT.Program) (ω : ℕ → ℝ) (w : ℕ) :
    (MinSumFPT.step (pre ++ compileAt pre.length cmd ++ suffix) d ω)^[cost]
        (s.state pre.length w) = t.state (pre.length+cmd.size) (w+cost) := by
  exact compileAt_simulates h _ ω pre.length w
    (contains_context pre (compileAt pre.length cmd) suffix)

/- An upper bound on structured costs becomes a bound on actual execution and
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
open StableMSR.Recovery.Compiler
theorem solution (cmd : Cmd) (result : ℕ) :
    DeterministicProgram (compile cmd result) ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (s t : Store) (cost : ℕ),
      Executes d cmd s t cost → ∀ (ω : ℕ → ℝ) (work : ℕ),
      (MinSumFPT.step (compile cmd result) d ω)^[cost+1] (s.state 0 work) =
        t.haltedState cmd.size (work+cost+1) result := by
  refine ⟨compile_deterministic cmd result,?_⟩
  intro n d s t cost h ω work
  exact compile_halts h ω work result
