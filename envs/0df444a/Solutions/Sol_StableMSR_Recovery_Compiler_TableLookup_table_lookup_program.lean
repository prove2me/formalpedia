-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.TableLookup.table_lookup_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-15T01:34:49.617641+00:00
-- url     : https://prove2.me/submissions/0e5621c3-5789-4f1b-b0b4-33b1d1b35852

import Definitions.Def_StableMSR_ComponentGraphMemory
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler
namespace StableMSR.Recovery.Compiler
lemma compile_deterministic (cmd : Cmd) (result : ℕ) :
    DeterministicProgram (compile cmd result) :=
  (compiler_execution_exact cmd result).1
lemma compile_halts {n : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {s t : Store} {cost : ℕ} (h : Executes d cmd s t cost)
    (ω : ℕ → ℝ) (w result : ℕ) :
    (MinSumFPT.step (compile cmd result) d ω)^[cost+1] (s.state 0 w) =
      t.haltedState cmd.size (w+cost+1) result :=
  (compiler_execution_exact cmd result).2 n d s t cost h ω w
@[simp] lemma compileAt_length (pc : ℕ) (cmd : Cmd) :
    (compileAt pc cmd).length = cmd.size := by
  induction cmd generalizing pc <;> simp_all [compileAt, Cmd.size] <;> omega
end StableMSR.Recovery.Compiler
namespace StableMSR.Recovery.ComponentMemory

@[simp] theorem address_eq_iff {n : ℕ} (base : ℤ) (u v : Fin n) :
    address base u = address base v ↔ u = v := by
  constructor
  · intro h
    apply Fin.ext
    have h' : (u.val : ℤ) = (v.val : ℤ) := by simpa [address] using h
    exact_mod_cast h'
  · rintro rfl
    rfl


end StableMSR.Recovery.ComponentMemory


open scoped Classical
namespace StableMSR.Recovery.Compiler.ComponentMachine

/- The graph bases and dimensions occupy registers 2--6; registers 7--14
are scratch. The command reads an ordinary directed edge list and two bitmaps. -/
def setPtr (s : Store) (i : ℕ) (z : ℤ) : Store :=
  { s with ptrs := Function.update s.ptrs i z }

def incPtr (s : Store) (i : ℕ) : Store := setPtr s i (s.ptrs i+1)

def opsCmd : List Op → Cmd
  | [] => .skip
  | op :: ops => .seq (.atom op) (opsCmd ops)

noncomputable def evalOps {N : ℕ} (d : Point N → Point N → ℝ) : List Op → Store → Store
  | [], s => s
  | op :: ops, s => evalOps d ops (op.eval d s)

lemma ops_exec {N : ℕ} (d : Point N → Point N → ℝ) (ops : List Op) (s : Store) :
    Executes d (opsCmd ops) s (evalOps d ops s) ops.length := by
  induction ops generalizing s with
  | nil => exact Executes.skip s
  | cons op ops ih =>
    simpa [opsCmd, evalOps, Nat.add_comm] using
      Executes.seq (Executes.atom op s) (ih (op.eval d s))

def nop : Cmd := .atom (.pointerCopy 0 0)
def pad2 : Cmd := .seq nop nop
def pad4 : Cmd := .seq pad2 pad2

lemma nop_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d nop s s 1 := by
  simpa [nop, Op.eval, Function.update_eq_self] using Executes.atom (Op.pointerCopy 0 0) s
lemma pad2_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d pad2 s s 2 := Executes.seq (nop_exec d s) (nop_exec d s)
lemma pad4_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d pad4 s s 4 := Executes.seq (pad2_exec d s) (pad2_exec d s)

/- Padding balances all three cases, including every branch and jump. -/
def markCmd : Cmd :=
  .ite (.pointerLE 13 0) pad4
    (.ite (.pointerLE 14 0) pad2 (.atom (.integerStore 11 1)))

noncomputable def markEval (s : Store) : Store :=
  if s.ptrs 13 ≤ s.ptrs 0 then s else
  if s.ptrs 14 ≤ s.ptrs 0 then s else
  { s with imem := Function.update s.imem (s.ptrs 11) (s.ptrs 1) }

lemma mark_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d markCmd s (markEval s) 5 := by
  by_cases h13 : s.ptrs 13 ≤ s.ptrs 0
  · simpa [markCmd, markEval, h13] using
      Executes.ite_true (c := Cond.pointerLE 13 0)
        (no := Cmd.ite (.pointerLE 14 0) pad2 (.atom (.integerStore 11 1)))
        h13 (pad4_exec d s)
  · by_cases h14 : s.ptrs 14 ≤ s.ptrs 0
    · simpa [markCmd, markEval, h13, h14] using
        Executes.ite_false (c := Cond.pointerLE 13 0) (yes := pad4) h13
          (Executes.ite_true (c := Cond.pointerLE 14 0)
            (no := Cmd.atom (.integerStore 11 1)) h14 (pad2_exec d s))
    · simpa [markCmd, markEval, h13, h14, Op.eval] using
        Executes.ite_false (c := Cond.pointerLE 13 0) (yes := pad4) h13
          (Executes.ite_false (c := Cond.pointerLE 14 0) (yes := pad2) h14
            (Executes.atom (.integerStore 11 1) s))

def edgeOps : List Op :=
  [.integerLoad 10 7, .pointerInc 7, .integerLoad 11 7, .pointerInc 7,
   .pointerAdd 10 4 10, .pointerAdd 12 3 11, .pointerAdd 11 4 11,
   .integerLoad 13 10, .integerLoad 14 12]

def edgeCmd : Cmd := .seq (opsCmd edgeOps) (.seq markCmd (.atom (.pointerInc 8)))

noncomputable def edgeInput (s : Store) : Store :=
  let a := s.imem (s.ptrs 7)
  let b := s.imem (s.ptrs 7+1)
  let t := setPtr (setPtr (setPtr (setPtr s 7 (s.ptrs 7+2))
    10 (s.ptrs 4+a)) 12 (s.ptrs 3+b)) 11 (s.ptrs 4+b)
  setPtr (setPtr t 13 (s.imem (s.ptrs 4+a))) 14 (s.imem (s.ptrs 3+b))

noncomputable def edgeStep (s : Store) : Store := incPtr (markEval (edgeInput s)) 8

lemma edgeInput_eq {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    evalOps d edgeOps s = edgeInput s := by
  simp [evalOps, edgeOps, Op.eval, edgeInput, setPtr, Function.update_comm,
    Function.update_idem, add_assoc]

lemma edge_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d edgeCmd s (edgeStep s) 15 := by
  have hp : Executes d (opsCmd edgeOps) s (edgeInput s) 9 := by
    have h := ops_exec d edgeOps s
    rw [edgeInput_eq] at h
    exact h
  exact Executes.seq hp (Executes.seq (mark_exec d _) (Executes.atom (.pointerInc 8) _))

lemma mark_ptrs (s : Store) : (markEval s).ptrs = s.ptrs := by
  simp only [markEval]; split <;> (try split) <;> rfl

lemma edge_ptr_frame (s : Store) (j : ℕ)
    (hj : j ≠ 7 ∧ j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 12 ∧ j ≠ 13 ∧ j ≠ 14) :
    (edgeStep s).ptrs j = s.ptrs j := by
  rcases hj with ⟨h7,h8,h10,h11,h12,h13,h14⟩
  simp [edgeStep, incPtr, setPtr, mark_ptrs, edgeInput,
    h7,h8,h10,h11,h12,h13,h14]

lemma edge_index (s : Store) : (edgeStep s).ptrs 8 = s.ptrs 8+1 := by
  simp [edgeStep, incPtr, setPtr, mark_ptrs, edgeInput]
lemma edge_cursor (s : Store) : (edgeStep s).ptrs 7 = s.ptrs 7+2 := by
  simp [edgeStep, incPtr, setPtr, mark_ptrs, edgeInput]

lemma iterate_preserves {α : Type*} (f : Store → Store) (F : Store → α)
    (h : ∀ s, F (f s) = F s) (q : ℕ) (s : Store) : F (f^[q] s) = F s := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Function.iterate_succ_apply',h,ih]

lemma iterate_additive (f : Store → Store) (F : Store → ℤ) (a : ℤ)
    (h : ∀ s, F (f s) = F s+a) (q : ℕ) (s : Store) :
    F (f^[q] s) = F s+(q:ℤ)*a := by
  induction q with
  | zero => simp
  | succ q ih => rw [Function.iterate_succ_apply',h,ih]; push_cast; ring

lemma fixed_loop_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (body : Cmd) (f : Store → Store) (i b cost : ℕ) (bound : ℤ)
    (he : ∀ s, s.ptrs b = bound → Executes d body s (f s) cost)
    (hi : ∀ s, (f s).ptrs i = s.ptrs i+1)
    (hbframe : ∀ s, (f s).ptrs b = s.ptrs b)
    (q : ℕ) (s : Store) (hb : s.ptrs b = bound)
    (hstop : s.ptrs i+(q:ℤ)-1 = bound) :
    Executes d (.whileDo (.pointerLE i b) body) s (f^[q] s) ((cost+2)*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test]
    omega
  | succ q ih =>
    have ht : (Cond.pointerLE i b).test s := by simp only [Cond.test]; omega
    have hrest := ih (f s) (by rw [hbframe,hb]) (by rw [hi]; push_cast at hstop; omega)
    have hrun := Executes.while_true ht (he s hb) hrest
    convert hrun using 1
    · exact Function.iterate_succ_apply f q s
    · simp only [Nat.mul_succ]; omega

def passSetupCmd : Cmd := opsCmd [.pointerCopy 7 2, .pointerConst 8 1]
def passSetup (s : Store) : Store := setPtr (setPtr s 7 (s.ptrs 2)) 8 1

def passCmd : Cmd := .seq passSetupCmd (.whileDo (.pointerLE 8 5) edgeCmd)
noncomputable def passEval (m : ℕ) (s : Store) : Store := edgeStep^[m] (passSetup s)

lemma pass_exec {N : ℕ} (d : Point N → Point N → ℝ) (m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) :
    Executes d passCmd s (passEval m s) (17*m+4) := by
  have hs : Executes d passSetupCmd s (passSetup s) 2 := by
    simpa [passSetupCmd, evalOps, Op.eval, passSetup, setPtr] using
      ops_exec d [.pointerCopy 7 2, .pointerConst 8 1] s
  have hl := fixed_loop_exec d edgeCmd edgeStep 8 5 15 m
    (fun t _ => edge_exec d t) edge_index
    (fun t => edge_ptr_frame t 5 (by norm_num)) m (passSetup s)
    (by simpa [passSetup,setPtr] using hm) (by simp [passSetup,setPtr])
  convert Executes.seq hs hl using 1 <;> try rfl
  omega

lemma pass_ptr_frame (m : ℕ) (s : Store) (j : ℕ)
    (hj : j ≠ 7 ∧ j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 12 ∧ j ≠ 13 ∧ j ≠ 14) :
    (passEval m s).ptrs j = s.ptrs j := by
  unfold passEval
  rw [iterate_preserves _ (fun t => t.ptrs j) (fun t => edge_ptr_frame t j hj)]
  simp [passSetup,setPtr,hj.1,hj.2.1]

lemma pass_cursor (m : ℕ) (s : Store) :
    (passEval m s).ptrs 7 = s.ptrs 2+2*(m:ℤ) := by
  unfold passEval
  rw [iterate_additive _ (fun t => t.ptrs 7) 2 edge_cursor]
  simp [passSetup,setPtr,mul_comm]

lemma pass_index (m : ℕ) (s : Store) : (passEval m s).ptrs 8 = (m:ℤ)+1 := by
  unfold passEval
  rw [iterate_additive _ (fun t => t.ptrs 8) 1 edge_index]
  simp [passSetup,setPtr,add_comm]

noncomputable def passStep (m : ℕ) (s : Store) : Store := incPtr (passEval m s) 9

def setupCmd : Cmd := opsCmd [.pointerConst 0 0, .pointerConst 1 1, .pointerConst 9 1]
def setup (s : Store) : Store := setPtr (setPtr (setPtr s 0 0) 1 1) 9 1

def block : Cmd := .seq setupCmd
  (.whileDo (.pointerLE 9 6) (.seq passCmd (.atom (.pointerInc 9))))
noncomputable def blockEval (m q : ℕ) (s : Store) : Store := (passStep m)^[q] (setup s)

lemma passStep_ptr_frame (m : ℕ) (s : Store) (j : ℕ)
    (hj : j < 7 ∨ 14 < j) : (passStep m s).ptrs j = s.ptrs j := by
  have h9 : j ≠ 9 := by omega
  simp only [passStep,incPtr,setPtr,Function.update_of_ne h9]
  apply pass_ptr_frame
  omega

lemma block_exec {N : ℕ} (d : Point N → Point N → ℝ) (m q : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 6 = (q:ℤ)) :
    Executes d block s (blockEval m q s) (q*(17*m+7)+5) := by
  have hs : Executes d setupCmd s (setup s) 3 := by
    simpa [setupCmd,evalOps,Op.eval,setup,setPtr] using
      ops_exec d [.pointerConst 0 0, .pointerConst 1 1, .pointerConst 9 1] s
  have hbody (t : Store) (ht : t.ptrs 5 = (m:ℤ)) :
      Executes d (.seq passCmd (.atom (.pointerInc 9))) t (passStep m t) (17*m+5) := by
    simpa [passStep,incPtr,setPtr,Op.eval,Nat.add_assoc] using
      Executes.seq (pass_exec d m t ht) (Executes.atom (.pointerInc 9) (passEval m t))
  have h5 (r : ℕ) : ((passStep m)^[r] (setup s)).ptrs 5 = (m:ℤ) := by
    rw [iterate_preserves _ (fun t => t.ptrs 5) (fun t => passStep_ptr_frame m t 5 (by omega))]
    simpa [setup,setPtr] using hm
  -- Induction carries the edge-count input as well as the outer-loop bound.
  have loop : ∀ (r : ℕ) (t : Store), t.ptrs 5 = (m:ℤ) → t.ptrs 6 = (q:ℤ) →
      t.ptrs 9+(r:ℤ)-1 = (q:ℤ) →
      Executes d (.whileDo (.pointerLE 9 6) (.seq passCmd (.atom (.pointerInc 9))))
        t ((passStep m)^[r] t) ((17*m+7)*r+2) := by
    intro r
    induction r with
    | zero =>
      intro t ht5 ht6 ht9
      apply Executes.while_false
      simp only [Cond.test]
      omega
    | succ r ih =>
      intro t ht5 ht6 ht9
      have hg : (Cond.pointerLE 9 6).test t := by simp only [Cond.test]; omega
      have ht9' : (passStep m t).ptrs 9 = t.ptrs 9+1 := by
        simp [passStep,incPtr,setPtr,pass_ptr_frame m t 9 (by norm_num)]
      have hr := ih (passStep m t)
        (by rw [passStep_ptr_frame m t 5 (by omega),ht5])
        (by rw [passStep_ptr_frame m t 6 (by omega),ht6])
        (by rw [ht9']; push_cast at ht9; omega)
      have hh := Executes.while_true hg (hbody t ht5) hr
      convert hh using 1
      · exact Function.iterate_succ_apply (passStep m) r t
      · simp only [Nat.mul_succ]; omega
  have hl := loop q (setup s) (by simpa [setup,setPtr] using hm)
    (by simpa [setup,setPtr] using hq) (by simp [setup,setPtr])
  convert Executes.seq hs hl using 1 <;> try rfl
  ring

lemma block_ptr_frame (m q : ℕ) (s : Store) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ 6 ∨ 14 < j) : (blockEval m q s).ptrs j = s.ptrs j := by
  unfold blockEval
  rw [iterate_preserves _ (fun t => t.ptrs j)
    (fun t => passStep_ptr_frame m t j (by omega))]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h9 : j ≠ 9 := by omega
  simp [setup,setPtr,h0,h1,h9]

/- Graph traversal changes integer scratch and reached flags only. -/
def DataFrame (s t : Store) : Prop :=
  t.regs = s.regs ∧ t.mem = s.mem ∧ t.queries = s.queries ∧
    t.tapePos = s.tapePos ∧ t.output = s.output

lemma DataFrame.refl (s : Store) : DataFrame s s := ⟨rfl,rfl,rfl,rfl,rfl⟩
lemma DataFrame.trans {s t u : Store} (h : DataFrame s t) (k : DataFrame t u) :
    DataFrame s u := ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
      k.2.2.2.1.trans h.2.2.2.1,k.2.2.2.2.trans h.2.2.2.2⟩

lemma setPtr_frame (s : Store) (i : ℕ) (z : ℤ) : DataFrame s (setPtr s i z) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
lemma incPtr_frame (s : Store) (i : ℕ) : DataFrame s (incPtr s i) :=
  setPtr_frame s i _
lemma edge_frame (s : Store) : DataFrame s (edgeStep s) := by
  unfold edgeStep incPtr setPtr markEval
  split <;> (try split) <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma iterate_frame (f : Store → Store) (h : ∀ t, DataFrame t (f t))
    (q : ℕ) (s : Store) : DataFrame s (f^[q] s) := by
  induction q with
  | zero => exact DataFrame.refl s
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (h _)

lemma pass_frame (m : ℕ) (s : Store) : DataFrame s (passEval m s) :=
  (show DataFrame s (passSetup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame edgeStep edge_frame m (passSetup s))

lemma passStep_frame (m : ℕ) (s : Store) : DataFrame s (passStep m s) :=
  (pass_frame m s).trans (incPtr_frame _ 9)

lemma block_frame (m q : ℕ) (s : Store) : DataFrame s (blockEval m q s) :=
  (show DataFrame s (setup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame (passStep m) (passStep_frame m) q (setup s))

lemma block_constants (m q : ℕ) (s : Store) :
    (blockEval m q s).ptrs 0 = 0 ∧ (blockEval m q s).ptrs 1 = 1 := by
  constructor
  · unfold blockEval
    rw [iterate_preserves _ (fun t => t.ptrs 0)
      (fun t => passStep_ptr_frame m t 0 (by omega))]
    simp [setup,setPtr]
  · unfold blockEval
    rw [iterate_preserves _ (fun t => t.ptrs 1)
      (fun t => passStep_ptr_frame m t 1 (by omega))]
    simp [setup,setPtr]

noncomputable def program : MinSumFPT.Program := compile block 0

lemma block_size : block.size = 33 := by decide
lemma program_length : program.length = 34 := by
  simp [program,compile,compileAt_length,block_size]

theorem kernel_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (m q : ℕ) (s : Store) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 6 = (q:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[q*(17*m+7)+6] (s.state 0 work) =
      (blockEval m q s).haltedState 33 (work+(q*(17*m+7)+6)) 0 := by
  simpa [program,block_size,Nat.add_assoc] using compile_halts (block_exec d m q s hm hq) ω work 0

theorem kernel_cubic_bound (n m : ℕ) (hm : m ≤ n^2) :
    n*(17*m+7)+6 ≤ 30*(n+1)^3 := by
  have hmul := Nat.mul_le_mul_left n hm
  nlinarith

/- A single finite graph-scanning program, with uniform source size and an
exact charged run on every edge-list dimension and requested pass count. -/
theorem kernel_uniform :
    program.length = 34 ∧ DeterministicProgram program ∧
    ∀ (N : ℕ) (d : Point N → Point N → ℝ) (m q : ℕ) (s : Store),
      s.ptrs 5 = (m:ℤ) → s.ptrs 6 = (q:ℤ) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      (MinSumFPT.step program d ω)^[q*(17*m+7)+6] (s.state 0 work) =
        (blockEval m q s).haltedState 33 (work+(q*(17*m+7)+6)) 0 := by
  exact ⟨program_length,compile_deterministic block 0,
    fun _ d m q s hm hq ω work => kernel_machine_execution d m q s hm hq ω work⟩

end StableMSR.Recovery.Compiler.ComponentMachine


set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.ArrayEquality

open ComponentMachine

def prepOps : List Op :=
  [.pointerConst 0 0, .pointerConst 18 1, .pointerCopy 20 6, .pointerDec 20]

def prepEval (s : Store) : Store :=
  setPtr (setPtr (setPtr s 0 0) 18 1) 20 (s.ptrs 6 - 1)

/- Two integer comparisons, with equal cost on equality and both strict orders. -/
def compareCmd : Cmd :=
  .ite (.pointerLE 21 22)
    (.ite (.pointerLE 22 21) pad2 (.atom (.pointerConst 18 0)))
    (.seq (.atom (.pointerConst 18 0)) nop)

def compareEval (s : Store) : Store :=
  if s.ptrs 21 = s.ptrs 22 then s else setPtr s 18 0

def body : Cmd :=
  .seq (opsCmd [.pointerAdd 23 3 20, .integerLoad 21 23,
    .pointerAdd 23 4 20, .integerLoad 22 23])
    (.seq compareCmd (.atom (.pointerDec 20)))

def inputEval (s : Store) : Store :=
  setPtr (setPtr (setPtr s 21 (s.imem (s.ptrs 3+s.ptrs 20)))
    23 (s.ptrs 4+s.ptrs 20)) 22 (s.imem (s.ptrs 4+s.ptrs 20))

def step (s : Store) : Store :=
  let t := compareEval (inputEval s)
  setPtr t 20 (t.ptrs 20-1)

def run : ℕ → Store → Store
  | 0, s => s
  | q+1, s => run q (step s)

def loop : Cmd := .whileDo (.pointerLE 0 20) body

def equalityCmd : Cmd := .seq (opsCmd prepOps) loop

def equalityEval (q : ℕ) (s : Store) : Store := run q (prepEval s)

@[simp] lemma equalityCmd_size : equalityCmd.size = 21 := rfl

lemma prep_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d (opsCmd prepOps) s (prepEval s) 4 := by
  simpa [prepOps,evalOps,prepEval,Op.eval,setPtr,Function.update_idem] using
    ops_exec d prepOps s

lemma compare_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d compareCmd s (compareEval s) 4 := by
  by_cases hle : s.ptrs 21 ≤ s.ptrs 22
  · by_cases hrev : s.ptrs 22 ≤ s.ptrs 21
    · have he := le_antisymm hle hrev
      simpa [compareCmd,compareEval,he] using
        Executes.ite_true (c := Cond.pointerLE 21 22)
          (no := Cmd.seq (.atom (.pointerConst 18 0)) nop) hle
          (Executes.ite_true (c := Cond.pointerLE 22 21)
            (no := Cmd.atom (.pointerConst 18 0)) hrev (pad2_exec d s))
    · have he : s.ptrs 21 ≠ s.ptrs 22 := by omega
      simpa [compareCmd,compareEval,he,Op.eval,setPtr] using
        Executes.ite_true (c := Cond.pointerLE 21 22)
          (no := Cmd.seq (.atom (.pointerConst 18 0)) nop) hle
          (Executes.ite_false (c := Cond.pointerLE 22 21) (yes := pad2) hrev
            (Executes.atom (.pointerConst 18 0) (d := d) s))
  · have he : s.ptrs 21 ≠ s.ptrs 22 := by omega
    have hp := Executes.seq (Executes.atom (.pointerConst 18 0) (d := d) s)
      (nop_exec d _)
    simpa [compareCmd,compareEval,he,Op.eval,setPtr] using
      Executes.ite_false (c := Cond.pointerLE 21 22)
        (yes := Cmd.ite (.pointerLE 22 21) pad2 (.atom (.pointerConst 18 0))) hle hp

lemma body_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d body s (step s) 9 := by
  have hi : Executes d (opsCmd [.pointerAdd 23 3 20, .integerLoad 21 23,
      .pointerAdd 23 4 20, .integerLoad 22 23]) s (inputEval s) 4 := by
    simpa [evalOps,Op.eval,inputEval,setPtr,Function.update_comm,Function.update_idem] using
      ops_exec d [.pointerAdd 23 3 20, .integerLoad 21 23,
        .pointerAdd 23 4 20, .integerLoad 22 23] s
  exact Executes.seq hi (Executes.seq (compare_exec d _)
    (Executes.atom (.pointerDec 20) _))

lemma step_ptr_frame (s : Store) (j : ℕ) (h18 : j ≠ 18) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) (h23 : j ≠ 23) :
    (step s).ptrs j = s.ptrs j := by
  simp only [step,compareEval]
  split <;> simp [setPtr,inputEval,h18,h20,h21,h22,h23]

lemma step_index (s : Store) : (step s).ptrs 20 = s.ptrs 20-1 := by
  simp only [step,compareEval]
  split <;> simp [setPtr,inputEval]

lemma step_flag (s : Store) :
    (step s).ptrs 18 =
      if s.imem (s.ptrs 3+s.ptrs 20) = s.imem (s.ptrs 4+s.ptrs 20)
      then s.ptrs 18 else 0 := by
  simp only [step,compareEval]
  split <;> simp_all [setPtr,inputEval]

lemma step_frame (s : Store) :
    (step s).regs = s.regs ∧ (step s).mem = s.mem ∧ (step s).imem = s.imem ∧
    (step s).queries = s.queries ∧ (step s).tapePos = s.tapePos ∧
    (step s).output = s.output := by
  simp only [step,compareEval]
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

lemma run_ptr_frame (q : ℕ) (s : Store) (j : ℕ) (h18 : j ≠ 18) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) (h23 : j ≠ 23) :
    (run q s).ptrs j = s.ptrs j := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => rw [run,ih,step_ptr_frame s j h18 h20 h21 h22 h23]

lemma run_frame (q : ℕ) (s : Store) :
    (run q s).regs = s.regs ∧ (run q s).mem = s.mem ∧ (run q s).imem = s.imem ∧
    (run q s).queries = s.queries ∧ (run q s).tapePos = s.tapePos ∧
    (run q s).output = s.output := by
  induction q generalizing s with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ q ih =>
    rcases ih (step s) with ⟨h1,h2,h3,h4,h5,h6⟩
    rcases step_frame s with ⟨g1,g2,g3,g4,g5,g6⟩
    exact ⟨h1.trans g1,h2.trans g2,h3.trans g3,h4.trans g4,h5.trans g5,h6.trans g6⟩

lemma loop_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (q : ℕ) (s : Store) (hzero : s.ptrs 0 = 0)
    (hindex : s.ptrs 20 = (q : ℤ)-1) :
    Executes d loop s (run q s) (11*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test,hzero,hindex,Nat.cast_zero]
    omega
  | succ q ih =>
    have hg : (Cond.pointerLE 0 20).test s := by
      simp only [Cond.test,hzero,hindex,Nat.cast_add,Nat.cast_one]
      omega
    have hz : (step s).ptrs 0 = 0 := by
      rw [step_ptr_frame s 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hzero
    have hi : (step s).ptrs 20 = (q : ℤ)-1 := by
      rw [step_index,hindex]
      push_cast
      omega
    have he := Executes.while_true hg (body_exec d s) (ih (step s) hz hi)
    simpa only [loop,run,show 1+9+1+(11*q+2)=11*(q+1)+2 by omega] using he

lemma equality_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    Executes d equalityCmd s (equalityEval q s) (11*q+6) := by
  have hz : (prepEval s).ptrs 0 = 0 := by simp [prepEval,setPtr]
  have hi : (prepEval s).ptrs 20 = (q : ℤ)-1 := by simp [prepEval,setPtr,hcount]
  have h := Executes.seq (prep_exec d s) (loop_exec d q (prepEval s) hz hi)
  simpa only [equalityCmd,equalityEval,show 4+(11*q+2)=11*q+6 by omega] using h

lemma equality_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (h0 : j ≠ 0) (h18 : j ≠ 18) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) (h23 : j ≠ 23) :
    (equalityEval q s).ptrs j = s.ptrs j := by
  rw [equalityEval,run_ptr_frame q (prepEval s) j h18 h20 h21 h22 h23]
  simp [prepEval,setPtr,h0,h18,h20]

lemma equality_frame (q : ℕ) (s : Store) :
    (equalityEval q s).regs = s.regs ∧ (equalityEval q s).mem = s.mem ∧
    (equalityEval q s).imem = s.imem ∧ (equalityEval q s).queries = s.queries ∧
    (equalityEval q s).tapePos = s.tapePos ∧ (equalityEval q s).output = s.output :=
  run_frame q (prepEval s)

end StableMSR.Recovery.Compiler.ArrayEquality


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Compiler.ArrayEquality

open ComponentMachine

def PrefixEqual (mem : ℤ → ℤ) (A B : ℤ) (q : ℕ) : Prop :=
  ∀ i : ℕ, i < q → mem (A+(i : ℤ)) = mem (B+(i : ℤ))

lemma prefixEqual_succ (mem : ℤ → ℤ) (A B : ℤ) (q : ℕ) :
    PrefixEqual mem A B (q+1) ↔
      PrefixEqual mem A B q ∧ mem (A+(q : ℤ)) = mem (B+(q : ℤ)) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega),h q (by omega)⟩
  · rintro ⟨hprefix,hlast⟩ i hi
    by_cases h : i < q
    · exact hprefix i h
    · have he : i = q := by omega
      simpa [he] using hlast

lemma prefixEqual_fin (mem : ℤ → ℤ) (A B : ℤ) (q : ℕ) :
    PrefixEqual mem A B q ↔
      ∀ i : Fin q, mem (A+(i.val : ℤ)) = mem (B+(i.val : ℤ)) := by
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h i hi
    exact h ⟨i,hi⟩

/- The flag is sticky: a mismatch sets zero permanently. -/
lemma run_flag (q : ℕ) (s : Store) (hindex : s.ptrs 20 = (q : ℤ)-1) :
    (run q s).ptrs 18 =
      if PrefixEqual s.imem (s.ptrs 3) (s.ptrs 4) q then s.ptrs 18 else 0 := by
  induction q generalizing s with
  | zero => simp [run,PrefixEqual]
  | succ q ih =>
    have hi : s.ptrs 20 = (q : ℤ) := by
      rw [hindex]
      push_cast
      omega
    have hnext : (step s).ptrs 20 = (q : ℤ)-1 := by rw [step_index,hi]
    rw [run,ih (step s) hnext,(step_frame s).2.2.1,
      step_ptr_frame s 3 (by decide) (by decide) (by decide) (by decide) (by decide),
      step_ptr_frame s 4 (by decide) (by decide) (by decide) (by decide) (by decide),
      step_flag,hi,prefixEqual_succ]
    by_cases hp : PrefixEqual s.imem (s.ptrs 3) (s.ptrs 4) q <;>
      by_cases hl : s.imem (s.ptrs 3+(q : ℤ)) = s.imem (s.ptrs 4+(q : ℤ)) <;>
        simp [hp,hl]

lemma equality_flag (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    (equalityEval q s).ptrs 18 =
      if (∀ i : Fin q, s.imem (s.ptrs 3+(i.val : ℤ)) =
        s.imem (s.ptrs 4+(i.val : ℤ))) then 1 else 0 := by
  have hi : (prepEval s).ptrs 20 = (q : ℤ)-1 := by simp [prepEval,setPtr,hcount]
  have h := run_flag q (prepEval s) hi
  simpa [equalityEval,prepEval,setPtr,prefixEqual_fin] using h

lemma equality_iff (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    (equalityEval q s).ptrs 18 = 1 ↔
      ∀ i : Fin q, s.imem (s.ptrs 3+(i.val : ℤ)) =
        s.imem (s.ptrs 4+(i.val : ℤ)) := by
  rw [equality_flag q s hcount]
  split <;> simp_all

lemma equality_flag_cases (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    (equalityEval q s).ptrs 18 = 0 ∨ (equalityEval q s).ptrs 18 = 1 := by
  rw [equality_flag q s hcount]
  split <;> simp

lemma equality_zero_iff (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    (equalityEval q s).ptrs 18 = 0 ↔
      ∃ i : Fin q, s.imem (s.ptrs 3+(i.val : ℤ)) ≠
        s.imem (s.ptrs 4+(i.val : ℤ)) := by
  rw [equality_flag q s hcount]
  split <;> simp_all

/- Uniform exact equality testing for arbitrary contiguous integer arrays. -/
theorem array_equality_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 22 ∧
      ∀ (N L : ℕ) (d : Point N → Point N → ℝ) (ω : ℕ → ℝ)
        (s : Store) (w : ℕ), s.ptrs 6 = (L : ℤ) →
        ∃ t : Store,
          (t.ptrs 18 = 0 ∨ t.ptrs 18 = 1) ∧
          (t.ptrs 18 = 1 ↔ ∀ i : Fin L,
            s.imem (s.ptrs 3+(i.val : ℤ)) = s.imem (s.ptrs 4+(i.val : ℤ))) ∧
          (t.ptrs 18 = 0 ↔ ∃ i : Fin L,
            s.imem (s.ptrs 3+(i.val : ℤ)) ≠ s.imem (s.ptrs 4+(i.val : ℤ))) ∧
          (∀ j : ℕ, j ≠ 0 → j ≠ 18 → j ≠ 20 →
            j ≠ 21 → j ≠ 22 → j ≠ 23 → t.ptrs j = s.ptrs j) ∧
          t.regs = s.regs ∧ t.mem = s.mem ∧ t.imem = s.imem ∧
          t.queries = s.queries ∧ t.tapePos = s.tapePos ∧ t.output = s.output ∧
          (MinSumFPT.step P d ω)^[11*L+7] (s.state 0 w) =
            t.haltedState 21 (w+(11*L+7)) 0 := by
  refine ⟨compile equalityCmd 0,compile_deterministic equalityCmd 0,?_,?_⟩
  · simp [compile]
  · intro N L d ω s w hcount
    refine ⟨equalityEval L s,equality_flag_cases L s hcount,
      equality_iff L s hcount,equality_zero_iff L s hcount,?_,?_⟩
    · intro j h0 h18 h20 h21 h22 h23
      exact equality_ptr_frame L s j h0 h18 h20 h21 h22 h23
    · rcases equality_frame L s with ⟨h1,h2,h3,h4,h5,h6⟩
      refine ⟨h1,h2,h3,h4,h5,h6,?_⟩
      have h := compile_halts (equality_exec d L s hcount) ω w 0
      simpa only [equalityCmd_size,show 11*L+6+1=11*L+7 by omega,
        show w+(11*L+6)+1=w+(11*L+7) by omega] using h

end StableMSR.Recovery.Compiler.ArrayEquality



open scoped Classical
namespace StableMSR.Recovery.Compiler.TableLookupMachine
open ComponentMachine ArrayEquality

/- Overwrite the saved result on a matching row, so later matches take
precedence. Both outcomes cost five instructions including branch control. -/
def matchOps : List Op :=
  [.pointerCopy 25 24, .pointerAdd 30 27 6, .integerLoad 26 30]

def matchCmd : Cmd := .ite (.pointerLE 18 32) pad4 (opsCmd matchOps)

noncomputable def matchEval (s : Store) : Store :=
  if s.ptrs 18 ≤ s.ptrs 32 then s else
    setPtr (setPtr (setPtr s 25 (s.ptrs 24)) 30 (s.ptrs 27+s.ptrs 6))
      26 (s.imem (s.ptrs 27+s.ptrs 6))

lemma match_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d matchCmd s (matchEval s) 5 := by
  by_cases h : s.ptrs 18 ≤ s.ptrs 32
  · simpa [matchCmd,matchEval,h] using
      Executes.ite_true (c := Cond.pointerLE 18 32) (no := opsCmd matchOps) h (pad4_exec d s)
  · have hm : Executes d (opsCmd matchOps) s
        (setPtr (setPtr (setPtr s 25 (s.ptrs 24)) 30 (s.ptrs 27+s.ptrs 6))
          26 (s.imem (s.ptrs 27+s.ptrs 6))) 3 := by
      simpa [matchOps,evalOps,Op.eval,setPtr] using ops_exec d matchOps s
    simpa [matchCmd,matchEval,h] using
      Executes.ite_false (c := Cond.pointerLE 18 32) (yes := pad4) h hm

def advanceCmd : Cmd := opsCmd [.pointerAdd 27 27 28, .pointerInc 24]
def advance (s : Store) : Store := incPtr (setPtr s 27 (s.ptrs 27+s.ptrs 28)) 24

lemma advance_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d advanceCmd s (advance s) 2 := by
  simpa [advanceCmd,advance,incPtr,setPtr,evalOps,Op.eval] using
    ops_exec d [.pointerAdd 27 27 28, .pointerInc 24] s

def rowCmd : Cmd := .seq (.atom (.pointerCopy 4 27))
  (.seq equalityCmd (.seq matchCmd advanceCmd))
noncomputable def rowEval (L : ℕ) (s : Store) : Store :=
  advance (matchEval (equalityEval L (setPtr s 4 (s.ptrs 27))))

lemma row_exec {N : ℕ} (d : Point N → Point N → ℝ) (L : ℕ) (s : Store)
    (hL : s.ptrs 6 = (L:ℤ)) :
    Executes d rowCmd s (rowEval L s) (11*L+14) := by
  have hL' : (setPtr s 4 (s.ptrs 27)).ptrs 6 = (L:ℤ) := by simpa [setPtr] using hL
  have h := Executes.seq (Executes.atom (.pointerCopy 4 27) s)
    (Executes.seq (equality_exec d L (setPtr s 4 (s.ptrs 27)) hL')
      (Executes.seq (match_exec d _) (advance_exec d _)))
  convert h using 1 <;> try rfl
  omega

lemma match_ptr_frame (s : Store) (j : ℕ)
    (h25 : j ≠ 25) (h26 : j ≠ 26) (h30 : j ≠ 30) :
    (matchEval s).ptrs j = s.ptrs j := by
  simp only [matchEval]
  split <;> simp [setPtr,h25,h26,h30]

lemma match_imem (s : Store) : (matchEval s).imem = s.imem := by
  simp only [matchEval]; split <;> rfl

lemma match_frame (s : Store) : DataFrame s (matchEval s) := by
  simp only [matchEval]; split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma advance_frame (s : Store) : DataFrame s (advance s) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma row_ptr_frame (L : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([0,4,18,20,21,22,23,24,25,26,27,30] : List ℕ)) :
    (rowEval L s).ptrs j = s.ptrs j := by
  have hh : j ≠ 0 ∧ j ≠ 4 ∧ j ≠ 18 ∧ j ≠ 20 ∧ j ≠ 21 ∧ j ≠ 22 ∧
      j ≠ 23 ∧ j ≠ 24 ∧ j ≠ 25 ∧ j ≠ 26 ∧ j ≠ 27 ∧ j ≠ 30 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hj
  rcases hh with ⟨h0,h4,h18,h20,h21,h22,h23,h24,h25,h26,h27,h30⟩
  simp only [rowEval,advance,incPtr,setPtr,Function.update_of_ne h24,
    Function.update_of_ne h27]
  rw [match_ptr_frame _ j h25 h26 h30,
    equality_ptr_frame L _ j h0 h18 h20 h21 h22 h23]
  simp [setPtr,h4]

lemma row_index (L : ℕ) (s : Store) : (rowEval L s).ptrs 24 = s.ptrs 24+1 := by
  simp [rowEval,advance,incPtr,setPtr,match_ptr_frame,equality_ptr_frame]

lemma row_cursor (L : ℕ) (s : Store) :
    (rowEval L s).ptrs 27 = s.ptrs 27+s.ptrs 28 := by
  simp [rowEval,advance,incPtr,setPtr,match_ptr_frame,equality_ptr_frame]

lemma row_imem (L : ℕ) (s : Store) : (rowEval L s).imem = s.imem := by
  simp only [rowEval,advance,incPtr,setPtr,match_imem]
  exact (equality_frame L _).2.2.1

lemma row_frame (L : ℕ) (s : Store) : DataFrame s (rowEval L s) := by
  have h := equality_frame L (setPtr s 4 (s.ptrs 27))
  have he : DataFrame s (equalityEval L (setPtr s 4 (s.ptrs 27))) :=
    ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
  exact he.trans ((match_frame _).trans (advance_frame _))

/- Store dimensions and ordinary table/query bases are the only inputs. -/
def setupOps : List Op :=
  [.pointerConst 24 0, .pointerCopy 25 5, .pointerConst 26 0,
   .pointerCopy 27 2, .pointerCopy 28 6, .pointerInc 28,
   .pointerCopy 29 5, .pointerDec 29, .pointerConst 32 0]
def setupCmd : Cmd := opsCmd setupOps

def setup (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr (setPtr (setPtr (setPtr s 24 0)
    25 (s.ptrs 5)) 26 0) 27 (s.ptrs 2)) 28 (s.ptrs 6+1)) 29 (s.ptrs 5-1)) 32 0

lemma setup_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d setupCmd s (setup s) 9 := by
  simpa [setupCmd,setupOps,setup,evalOps,Op.eval,setPtr,Function.update_idem] using
    ops_exec d setupOps s

def block : Cmd := .seq setupCmd (.whileDo (.pointerLE 24 29) rowCmd)
noncomputable def blockEval (L q : ℕ) (s : Store) : Store := (rowEval L)^[q] (setup s)

lemma block_exec {N : ℕ} (d : Point N → Point N → ℝ) (L q : ℕ) (s : Store)
    (hL : s.ptrs 6 = (L:ℤ)) (hq : s.ptrs 5 = (q:ℤ)) :
    Executes d block s (blockEval L q s) (q*(11*L+16)+11) := by
  have loop : ∀ (r : ℕ) (t : Store), t.ptrs 6 = (L:ℤ) →
      t.ptrs 24+(r:ℤ)-1 = t.ptrs 29 →
      Executes d (.whileDo (.pointerLE 24 29) rowCmd)
        t ((rowEval L)^[r] t) ((11*L+16)*r+2) := by
    intro r
    induction r with
    | zero =>
      intro t htL htstop
      apply Executes.while_false
      simp only [Cond.test]
      omega
    | succ r ih =>
      intro t htL htstop
      have hg : (Cond.pointerLE 24 29).test t := by simp only [Cond.test]; omega
      have hr := ih (rowEval L t)
        (by rw [row_ptr_frame L t 6 (by simp),htL])
        (by rw [row_index,row_ptr_frame L t 29 (by simp)]; push_cast at htstop; omega)
      have hh := Executes.while_true hg (row_exec d L t htL) hr
      convert hh using 1
      · exact Function.iterate_succ_apply (rowEval L) r t
      · simp only [Nat.mul_succ]; omega
  have hl := loop q (setup s) (by simpa [setup,setPtr] using hL)
    (by simp [setup,setPtr,hq])
  convert Executes.seq (setup_exec d s) hl using 1 <;> try rfl
  ring

lemma block_frame (L q : ℕ) (s : Store) : DataFrame s (blockEval L q s) :=
  (show DataFrame s (setup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame (rowEval L) (row_frame L) q (setup s))

lemma block_imem (L q : ℕ) (s : Store) : (blockEval L q s).imem = s.imem := by
  unfold blockEval
  rw [iterate_preserves _ Store.imem (row_imem L)]
  rfl

lemma block_ptr_frame (L q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([0,4,18,20,21,22,23,24,25,26,27,28,29,30,32] : List ℕ)) :
    (blockEval L q s).ptrs j = s.ptrs j := by
  have hrow : j ∉ ([0,4,18,20,21,22,23,24,25,26,27,30] : List ℕ) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hj ⊢
    tauto
  unfold blockEval
  rw [iterate_preserves _ (fun t => t.ptrs j) (fun t => row_ptr_frame L t j hrow)]
  have h24 : j ≠ 24 := by simp_all
  have h25 : j ≠ 25 := by simp_all
  have h26 : j ≠ 26 := by simp_all
  have h27 : j ≠ 27 := by simp_all
  have h28 : j ≠ 28 := by simp_all
  have h29 : j ≠ 29 := by simp_all
  have h32 : j ≠ 32 := by simp_all
  simp [setup,setPtr,h24,h25,h26,h27,h28,h29,h32]

noncomputable def program : MinSumFPT.Program := compile block 0
lemma block_size : block.size = 45 := by decide
lemma program_length : program.length = 46 := by
  simp [program,compile,compileAt_length,block_size]

theorem lookup_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (L q : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) (hq : s.ptrs 5 = (q:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[q*(11*L+16)+12] (s.state 0 work) =
      (blockEval L q s).haltedState 45 (work+(q*(11*L+16)+12)) 0 := by
  simpa [program,block_size,Nat.add_assoc] using compile_halts (block_exec d L q s hL hq) ω work 0

end StableMSR.Recovery.Compiler.TableLookupMachine



namespace StableMSR.Recovery.TableLookupSemantics

/- An ordinary fixed-width record is its key followed by one payload cell. -/
def rowBase (tableBase : ℤ) (width row : ℕ) : ℤ :=
  tableBase + (row : ℤ) * ((width : ℤ) + 1)

def rowMatches (mem : ℤ → ℤ) (tableBase queryBase : ℤ)
    (width row : ℕ) : Prop :=
  ∀ j : Fin width, mem (queryBase + (j.val : ℤ)) =
    mem (rowBase tableBase width row + (j.val : ℤ))

instance (mem : ℤ → ℤ) (tableBase queryBase : ℤ) (width row : ℕ) :
    Decidable (rowMatches mem tableBase queryBase width row) :=
  inferInstanceAs (Decidable (∀ j : Fin width, mem (queryBase + (j.val : ℤ)) =
    mem (rowBase tableBase width row + (j.val : ℤ))))

def rowPayload (mem : ℤ → ℤ) (tableBase : ℤ) (width row : ℕ) : ℤ :=
  mem (rowBase tableBase width row + (width : ℤ))

/- Sequential scan with overwrite-on-match: later matching rows take priority. -/
def scan (hit : ℕ → Prop) [DecidablePred hit]
    (payload : ℕ → ℤ) (sentinel : ℕ) : ℕ → ℕ × ℤ
  | 0 => (sentinel, 0)
  | r + 1 => if hit r then (r, payload r) else scan hit payload sentinel r

theorem scan_spec (hit : ℕ → Prop) [DecidablePred hit]
    (payload : ℕ → ℤ) (sentinel r : ℕ) :
    (scan hit payload sentinel r = (sentinel, 0) ∧
      ∀ i < r, ¬ hit i) ∨
    ∃ i < r, hit i ∧ scan hit payload sentinel r = (i, payload i) ∧
      ∀ j < r, hit j → j ≤ i := by
  induction r with
  | zero => exact Or.inl ⟨rfl, by omega⟩
  | succ r ih =>
    by_cases hm : hit r
    · exact Or.inr ⟨r, by omega, hm, by simp [scan,hm], by omega⟩
    · simp only [scan,if_neg hm]
      rcases ih with ⟨he,hn⟩ | ⟨i,hi,hmi,he,hmax⟩
      · refine Or.inl ⟨he,?_⟩
        intro i hi hmi
        by_cases hir : i = r
        · exact hm (hir ▸ hmi)
        · exact hn i (by omega) hmi
      · refine Or.inr ⟨i,by omega,hmi,he,?_⟩
        intro j hj hmj
        have hjr : j ≠ r := fun h => hm (h ▸ hmj)
        exact hmax j (by omega) hmj

theorem scan_sentinel_iff (hit : ℕ → Prop) [DecidablePred hit]
    (payload : ℕ → ℤ) (sentinel r : ℕ) (hr : r ≤ sentinel) :
    (scan hit payload sentinel r).1 = sentinel ↔ ∀ i < r, ¬ hit i := by
  rcases scan_spec hit payload sentinel r with ⟨he,hn⟩ | ⟨i,hi,hmi,he,_⟩
  · constructor
    · intro _; exact hn
    · intro _; simp [he]
  · rw [he]
    constructor
    · intro h
      simp only at h
      omega
    · intro h
      exact (h i hi hmi).elim

theorem scan_sentinel_payload (hit : ℕ → Prop) [DecidablePred hit]
    (payload : ℕ → ℤ) (sentinel r : ℕ) (hr : r ≤ sentinel)
    (h : (scan hit payload sentinel r).1 = sentinel) :
    (scan hit payload sentinel r).2 = 0 := by
  have hn := (scan_sentinel_iff hit payload sentinel r hr).mp h
  rcases scan_spec hit payload sentinel r with ⟨he,_⟩ | ⟨i,hi,hmi,_⟩
  · simp [he]
  · exact (hn i hi hmi).elim

theorem scan_last_match (hit : ℕ → Prop) [DecidablePred hit]
    (payload : ℕ → ℤ) (sentinel r : ℕ)
    (h : (scan hit payload sentinel r).1 ≠ sentinel) :
    (scan hit payload sentinel r).1 < r ∧
    hit (scan hit payload sentinel r).1 ∧
    (scan hit payload sentinel r).2 = payload (scan hit payload sentinel r).1 ∧
    ∀ j < r, hit j → j ≤ (scan hit payload sentinel r).1 := by
  rcases scan_spec hit payload sentinel r with ⟨he,_⟩ | ⟨i,hi,hmi,he,hmax⟩
  · exact (h (by simp [he])).elim
  · rw [he]
    exact ⟨hi,hmi,rfl,hmax⟩

theorem scan_eq_of_last (hit : ℕ → Prop) [DecidablePred hit]
    (payload : ℕ → ℤ) (sentinel r i : ℕ) (hi : i < r) (hm : hit i)
    (hmax : ∀ j < r, hit j → j ≤ i) :
    scan hit payload sentinel r = (i, payload i) := by
  rcases scan_spec hit payload sentinel r with ⟨_,hn⟩ | ⟨j,hj,hmj,he,hjmax⟩
  · exact (hn i hi hm).elim
  · have hij : i = j := Nat.le_antisymm (hjmax i hi hm) (hmax j hj hmj)
    simpa [hij] using he

theorem scan_eq_of_unique (hit : ℕ → Prop) [DecidablePred hit]
    (payload : ℕ → ℤ) (sentinel r i : ℕ) (hi : i < r) (hm : hit i)
    (hunique : ∀ j < r, hit j → j = i) :
    scan hit payload sentinel r = (i, payload i) :=
  scan_eq_of_last hit payload sentinel r i hi hm
    (fun j hj hmj => Nat.le_of_eq (hunique j hj hmj))

@[simp] theorem rowMatches_zero (mem : ℤ → ℤ) (tableBase queryBase : ℤ) (row : ℕ) :
    rowMatches mem tableBase queryBase 0 row := by
  intro j
  exact Fin.elim0 j

theorem scan_zero_width_succ (mem : ℤ → ℤ) (tableBase queryBase : ℤ)
    (sentinel r : ℕ) :
    scan (rowMatches mem tableBase queryBase 0)
      (rowPayload mem tableBase 0) sentinel (r+1) =
        (r, mem (tableBase + (r : ℤ))) := by
  simp [scan,rowMatches_zero,rowPayload,rowBase]

end StableMSR.Recovery.TableLookupSemantics



open scoped Classical
namespace StableMSR.Recovery.Compiler.TableLookupMachine
open ComponentMachine ArrayEquality

lemma match_result_index (s : Store) :
    (matchEval s).ptrs 25 = if s.ptrs 18 ≤ s.ptrs 32 then s.ptrs 25 else s.ptrs 24 := by
  simp only [matchEval]
  split <;> simp_all [setPtr]

lemma match_result_payload (s : Store) :
    (matchEval s).ptrs 26 = if s.ptrs 18 ≤ s.ptrs 32 then s.ptrs 26
      else s.imem (s.ptrs 27+s.ptrs 6) := by
  simp only [matchEval]
  split <;> simp_all [setPtr]

/- The actual array-comparison call controls precisely the two saved outputs. -/
lemma row_results (L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) (hz : s.ptrs 32 = 0) :
    (rowEval L s).ptrs 25 =
      (if ∀ j : Fin L, s.imem (s.ptrs 3+(j.val:ℤ)) = s.imem (s.ptrs 27+(j.val:ℤ))
        then s.ptrs 24 else s.ptrs 25) ∧
    (rowEval L s).ptrs 26 =
      (if ∀ j : Fin L, s.imem (s.ptrs 3+(j.val:ℤ)) = s.imem (s.ptrs 27+(j.val:ℤ))
        then s.imem (s.ptrs 27+s.ptrs 6) else s.ptrs 26) := by
  let t := setPtr s 4 (s.ptrs 27)
  have ht : t.ptrs 6 = (L:ℤ) := by simpa [t,setPtr] using hL
  have hflag : (equalityEval L t).ptrs 18 =
      if ∀ j : Fin L, s.imem (s.ptrs 3+(j.val:ℤ)) = s.imem (s.ptrs 27+(j.val:ℤ))
        then 1 else 0 := by
    simpa [t,setPtr] using equality_flag L t ht
  have hp (j : ℕ) (h0 : j ≠ 0) (h4 : j ≠ 4) (h18 : j ≠ 18)
      (h20 : j ≠ 20) (h21 : j ≠ 21) (h22 : j ≠ 22) (h23 : j ≠ 23) :
      (equalityEval L t).ptrs j = s.ptrs j := by
    rw [equality_ptr_frame L t j h0 h18 h20 h21 h22 h23]
    simp [t,setPtr,h4]
  have h32 : (equalityEval L t).ptrs 32 = 0 := by
    rw [hp 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),hz]
  have him : (equalityEval L t).imem = s.imem := (equality_frame L t).2.2.1
  change (matchEval (equalityEval L t)).ptrs 25 = _ ∧
    (matchEval (equalityEval L t)).ptrs 26 = _
  rw [match_result_index,match_result_payload,hflag,h32,him]
  rw [hp 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hp 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hp 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hp 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hp 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  split <;> simp_all

end StableMSR.Recovery.Compiler.TableLookupMachine


open scoped Classical
namespace StableMSR.Recovery.Compiler.TableLookup

open StableMSR.Recovery.Compiler.ComponentMachine (setPtr iterate_additive iterate_preserves)
open TableLookupMachine TableLookupSemantics

theorem block_index (L r : ℕ) (s : Store) :
    (blockEval L r s).ptrs 24 = (r : ℤ) := by
  unfold blockEval
  rw [iterate_additive _ (fun t => t.ptrs 24) 1 (row_index L)]
  simp [TableLookupMachine.setup,setPtr]

theorem block_stride (L r : ℕ) (s : Store) :
    (blockEval L r s).ptrs 28 = s.ptrs 6 + 1 := by
  unfold blockEval
  rw [iterate_preserves _ (fun t => t.ptrs 28)
    (fun t => row_ptr_frame L t 28 (by simp))]
  simp [TableLookupMachine.setup,setPtr]

theorem block_zero (L r : ℕ) (s : Store) :
    (blockEval L r s).ptrs 32 = 0 := by
  unfold blockEval
  rw [iterate_preserves _ (fun t => t.ptrs 32)
    (fun t => row_ptr_frame L t 32 (by simp))]
  simp [TableLookupMachine.setup,setPtr]

theorem block_cursor (L r : ℕ) (s : Store) :
    (blockEval L r s).ptrs 27 = s.ptrs 2 + (r : ℤ) * (s.ptrs 6 + 1) := by
  induction r with
  | zero => simp [blockEval,TableLookupMachine.setup,setPtr]
  | succ r ih =>
    simp only [blockEval,Function.iterate_succ_apply']
    rw [row_cursor]
    change (blockEval L r s).ptrs 27 + (blockEval L r s).ptrs 28 = _
    rw [ih,block_stride]
    push_cast
    ring

/- The actual saved row and payload agree with the pure sequential scan. -/
theorem block_scan (L q r : ℕ) (s : Store)
    (hL : s.ptrs 6 = (L : ℤ)) (hq : s.ptrs 5 = (q : ℤ)) :
    (blockEval L r s).ptrs 25 =
      ((scan (rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L)
        (rowPayload s.imem (s.ptrs 2) L) q r).1 : ℤ) ∧
    (blockEval L r s).ptrs 26 =
      (scan (rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L)
        (rowPayload s.imem (s.ptrs 2) L) q r).2 := by
  induction r with
  | zero => simp [blockEval,TableLookupMachine.setup,setPtr,scan,hq]
  | succ r ih =>
    have h6 : (blockEval L r s).ptrs 6 = (L : ℤ) := by
      rw [block_ptr_frame L r s 6 (by simp),hL]
    have h3 : (blockEval L r s).ptrs 3 = s.ptrs 3 :=
      block_ptr_frame L r s 3 (by simp)
    have hc : (blockEval L r s).ptrs 27 = rowBase (s.ptrs 2) L r := by
      rw [block_cursor,hL]
      rfl
    have hr := row_results L (blockEval L r s) h6 (block_zero L r s)
    rw [block_imem,h3,hc,block_index,h6,ih.1,ih.2] at hr
    simp only [blockEval,Function.iterate_succ_apply']
    change (rowEval L (blockEval L r s)).ptrs 25 = _ ∧
      (rowEval L (blockEval L r s)).ptrs 26 = _
    rw [hr.1,hr.2]
    by_cases hh : rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L r
    · simp [scan,rowMatches] at hh ⊢
      simp [hh,rowPayload]
    · simp only [rowMatches] at hh
      simp [scan,rowMatches,hh,rowPayload]

theorem block_lookup_sentinel (L q : ℕ) (s : Store)
    (hL : s.ptrs 6 = (L : ℤ)) (hq : s.ptrs 5 = (q : ℤ)) :
    (blockEval L q s).ptrs 25 = (q : ℤ) ↔
      ∀ i < q, ¬ rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L i := by
  rw [(block_scan L q q s hL hq).1,Nat.cast_inj]
  exact scan_sentinel_iff _ _ q q (le_refl _)

theorem block_lookup_no_payload (L q : ℕ) (s : Store)
    (hL : s.ptrs 6 = (L : ℤ)) (hq : s.ptrs 5 = (q : ℤ))
    (hn : (blockEval L q s).ptrs 25 = (q : ℤ)) :
    (blockEval L q s).ptrs 26 = 0 := by
  have hs := block_scan L q q s hL hq
  rw [hs.1,Nat.cast_inj] at hn
  rw [hs.2]
  exact scan_sentinel_payload _ _ q q (le_refl _) hn

theorem block_lookup_hit (L q : ℕ) (s : Store)
    (hL : s.ptrs 6 = (L : ℤ)) (hq : s.ptrs 5 = (q : ℤ))
    (hn : (blockEval L q s).ptrs 25 ≠ (q : ℤ)) :
    ∃ i : Fin q, (blockEval L q s).ptrs 25 = (i.val : ℤ) ∧
      rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L i.val ∧
      (blockEval L q s).ptrs 26 = rowPayload s.imem (s.ptrs 2) L i.val ∧
      ∀ j : Fin q, rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L j.val → j.val ≤ i.val := by
  have hs := block_scan L q q s hL hq
  simp only [hs.1,ne_eq,Nat.cast_inj] at hn
  have hh := scan_last_match (rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L)
    (rowPayload s.imem (s.ptrs 2) L) q q hn
  refine ⟨⟨_,hh.1⟩,hs.1,hh.2.1,hs.2.trans hh.2.2.1,?_⟩
  intro j hj
  exact hh.2.2.2 j.val j.isLt hj

theorem block_lookup_bounds (L q : ℕ) (s : Store)
    (hL : s.ptrs 6 = (L : ℤ)) (hq : s.ptrs 5 = (q : ℤ)) :
    0 ≤ (blockEval L q s).ptrs 25 ∧ (blockEval L q s).ptrs 25 ≤ (q : ℤ) := by
  by_cases hn : (blockEval L q s).ptrs 25 = (q : ℤ)
  · rw [hn]
    exact ⟨Nat.cast_nonneg _,le_refl _⟩
  · obtain ⟨i,hi,_⟩ := block_lookup_hit L q s hL hq hn
    rw [hi]
    exact ⟨Nat.cast_nonneg _,Nat.cast_le.mpr (Nat.le_of_lt i.isLt)⟩

theorem block_lookup_unique (L q : ℕ) (s : Store)
    (hL : s.ptrs 6 = (L : ℤ)) (hq : s.ptrs 5 = (q : ℤ)) (i : Fin q)
    (hm : rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L i.val)
    (hunique : ∀ j : Fin q, rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L j.val → j = i) :
    (blockEval L q s).ptrs 25 = (i.val : ℤ) ∧
      (blockEval L q s).ptrs 26 = rowPayload s.imem (s.ptrs 2) L i.val := by
  have he := scan_eq_of_unique (rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L)
    (rowPayload s.imem (s.ptrs 2) L) q q i.val i.isLt hm
    (fun j hj hh => congrArg Fin.val (hunique ⟨j,hj⟩ hh))
  simpa only [he] using block_scan L q q s hL hq

theorem block_lookup_zero_rows (L : ℕ) (s : Store) (hq : s.ptrs 5 = 0) :
    (blockEval L 0 s).ptrs 25 = 0 ∧ (blockEval L 0 s).ptrs 26 = 0 := by
  simp [blockEval,TableLookupMachine.setup,setPtr,hq]

theorem block_lookup_zero_width (q : ℕ) (s : Store)
    (hL : s.ptrs 6 = 0) (hq : s.ptrs 5 = ((q+1 : ℕ) : ℤ)) :
    (blockEval 0 (q+1) s).ptrs 25 = (q : ℤ) ∧
      (blockEval 0 (q+1) s).ptrs 26 = s.imem (s.ptrs 2 + (q : ℤ)) := by
  simpa only [scan_zero_width_succ] using block_scan 0 (q+1) (q+1) s hL hq

/- A fixed finite program scans ordinary integer records, returning the last
matching row and its actual payload. Zero rows and zero-width keys are allowed;
no assumptions are made about the initial scratch registers or memory contents. -/
end StableMSR.Recovery.Compiler.TableLookup

open StableMSR.Recovery.Compiler.TableLookup StableMSR.Recovery.ComponentMemory StableMSR.Recovery.Compiler.TableLookupMachine StableMSR.Recovery.TableLookupSemantics
theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 46 ∧
    ∀ (N q L : ℕ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 5 = (q : ℤ) → s.ptrs 6 = (L : ℤ) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let result := (MinSumFPT.step P d ω)^[q*(11*L+16)+12] (s.state 0 work)
      result.halted = true ∧ result.work = work+(q*(11*L+16)+12) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧ result.imem = s.imem ∧
      (result.cfg.ptrs 25 = (q : ℤ) ↔
        ∀ i : Fin q, ¬ (∀ j : Fin L, s.imem (s.ptrs 3+(j.val : ℤ)) =
          s.imem (s.ptrs 2+(i.val : ℤ)*((L : ℤ)+1)+(j.val : ℤ)))) ∧
      (result.cfg.ptrs 25 = (q : ℤ) → result.cfg.ptrs 26 = 0) ∧
      (result.cfg.ptrs 25 ≠ (q : ℤ) →
        ∃ i : Fin q, result.cfg.ptrs 25 = (i.val : ℤ) ∧
          (∀ j : Fin L, s.imem (s.ptrs 3+(j.val : ℤ)) =
            s.imem (s.ptrs 2+(i.val : ℤ)*((L : ℤ)+1)+(j.val : ℤ))) ∧
          result.cfg.ptrs 26 = s.imem (s.ptrs 2+(i.val : ℤ)*((L : ℤ)+1)+(L : ℤ)) ∧
          ∀ k : Fin q, (∀ j : Fin L, s.imem (s.ptrs 3+(j.val : ℤ)) =
            s.imem (s.ptrs 2+(k.val : ℤ)*((L : ℤ)+1)+(j.val : ℤ))) →
              k.val ≤ i.val) ∧
      (0 ≤ result.cfg.ptrs 25 ∧ result.cfg.ptrs 25 ≤ (q : ℤ)) ∧
      (∀ j : ℕ, j ∉ ([0,4,18,20,21,22,23,24,25,26,27,28,29,30,32] : List ℕ) →
        result.cfg.ptrs j = s.ptrs j) := by
  refine ⟨TableLookupMachine.program,compile_deterministic TableLookupMachine.block 0,
    TableLookupMachine.program_length,?_⟩
  intro N q L d s hq hL ω work
  dsimp only
  rw [lookup_machine_execution d L q s hL hq ω work]
  have hf := TableLookupMachine.block_frame L q s
  refine ⟨rfl,rfl,hf.2.2.1,hf.2.2.2.1,hf.2.1,hf.1,block_imem L q s,?_,
    block_lookup_no_payload L q s hL hq,?_,block_lookup_bounds L q s hL hq,
    block_ptr_frame L q s⟩
  · change (blockEval L q s).ptrs 25 = (q : ℤ) ↔
      ∀ i : Fin q, ¬ rowMatches s.imem (s.ptrs 2) (s.ptrs 3) L i.val
    rw [block_lookup_sentinel L q s hL hq]
    constructor
    · intro h i
      exact h i.val i.isLt
    · intro h i hi
      exact h ⟨i,hi⟩
  · simpa only [rowMatches,rowPayload,rowBase,Store.haltedState,Store.state]
      using block_lookup_hit L q s hL hq

