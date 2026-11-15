-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.TableAppend.table_append_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-15T03:01:10.186348+00:00
-- url     : https://prove2.me/submissions/80466a4d-d5c0-44d5-8736-90f7830f1688

import Definitions.Def_StableMSR_StructuredCompiler
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

namespace StableMSR.Recovery.Compiler.ArrayCopy
open ComponentMachine

/- Copy one integer cell and advance both cursors and the loop counter. -/
def bodyOps : List Op :=
  [.integerLoad 38 34, .integerStore 35 38, .pointerInc 34,
   .pointerInc 35, .pointerInc 37]
def body : Cmd := opsCmd bodyOps

def copyOne (s : Store) : Store :=
  { s with
    imem := Function.update s.imem (s.ptrs 35) (s.imem (s.ptrs 34))
    ptrs := Function.update (Function.update (Function.update (Function.update s.ptrs
      38 (s.imem (s.ptrs 34))) 34 (s.ptrs 34+1)) 35 (s.ptrs 35+1)) 37 (s.ptrs 37+1) }

def run : ℕ → Store → Store
  | 0, s => s
  | q+1, s => run q (copyOne s)

lemma body_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d body s (copyOne s) 5 := by
  simpa [body,bodyOps,evalOps,Op.eval,copyOne,Function.update_comm,
    Function.update_idem] using ops_exec d bodyOps s

@[simp] lemma copyOne_src (s : Store) : (copyOne s).ptrs 34 = s.ptrs 34+1 := by
  simp [copyOne]
@[simp] lemma copyOne_dst (s : Store) : (copyOne s).ptrs 35 = s.ptrs 35+1 := by
  simp [copyOne]
@[simp] lemma copyOne_index (s : Store) : (copyOne s).ptrs 37 = s.ptrs 37+1 := by
  simp [copyOne]
lemma copyOne_ptr_frame (s : Store) (j : ℕ)
    (h34 : j ≠ 34) (h35 : j ≠ 35) (h37 : j ≠ 37) (h38 : j ≠ 38) :
    (copyOne s).ptrs j = s.ptrs j := by simp [copyOne,h34,h35,h37,h38]
lemma copyOne_frame (s : Store) : DataFrame s (copyOne s) := ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma run_src (q : ℕ) (s : Store) : (run q s).ptrs 34 = s.ptrs 34+(q:ℤ) := by
  induction q generalizing s with
  | zero => simp [run]
  | succ q ih => rw [run,ih,copyOne_src]; push_cast; ring
lemma run_dst (q : ℕ) (s : Store) : (run q s).ptrs 35 = s.ptrs 35+(q:ℤ) := by
  induction q generalizing s with
  | zero => simp [run]
  | succ q ih => rw [run,ih,copyOne_dst]; push_cast; ring
lemma run_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (h34 : j ≠ 34) (h35 : j ≠ 35) (h37 : j ≠ 37) (h38 : j ≠ 38) :
    (run q s).ptrs j = s.ptrs j := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => rw [run,ih,copyOne_ptr_frame s j h34 h35 h37 h38]
lemma run_frame (q : ℕ) (s : Store) : DataFrame s (run q s) := by
  induction q generalizing s with
  | zero => exact DataFrame.refl _
  | succ q ih => exact (copyOne_frame s).trans (ih (copyOne s))

/- The final memory outside the destination interval is unchanged. -/
lemma run_memory_frame (q : ℕ) (s : Store) (x : ℤ)
    (hx : x < s.ptrs 35 ∨ s.ptrs 35+(q:ℤ) ≤ x) :
    (run q s).imem x = s.imem x := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih =>
    have hnext : x < (copyOne s).ptrs 35 ∨
        (copyOne s).ptrs 35+(q:ℤ) ≤ x := by rw [copyOne_dst]; push_cast at hx; omega
    rw [run,ih (copyOne s) hnext]
    have hne : x ≠ s.ptrs 35 := by push_cast at hx; omega
    exact Function.update_of_ne hne _ _

/- Disjoint source and destination intervals give snapshot-copy semantics. -/
lemma run_memory_get (q : ℕ) (s : Store)
    (hsep : ∀ i j : Fin q, s.ptrs 34+(i.val:ℤ) ≠ s.ptrs 35+(j.val:ℤ))
    (i : Fin q) :
    (run q s).imem (s.ptrs 35+(i.val:ℤ)) = s.imem (s.ptrs 34+(i.val:ℤ)) := by
  induction q generalizing s with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    have hn : (s.ptrs 34) ≠ s.ptrs 35 := by
      simpa using hsep ⟨0,by omega⟩ ⟨0,by omega⟩
    by_cases hi : i.val = 0
    · have hx : s.ptrs 35 < (copyOne s).ptrs 35 := by simp
      have hf := run_memory_frame q (copyOne s) (s.ptrs 35) (Or.inl hx)
      simpa [run,hi,copyOne] using hf
    · let j : Fin q := ⟨i.val-1,by omega⟩
      have he : (copyOne s).ptrs 35+(j.val:ℤ) = s.ptrs 35+(i.val:ℤ) := by
        simp only [copyOne_dst]; dsimp [j]; omega
      have hs : ∀ a b : Fin q,
          (copyOne s).ptrs 34+(a.val:ℤ) ≠ (copyOne s).ptrs 35+(b.val:ℤ) := by
        intro a b
        simpa only [copyOne_src,copyOne_dst,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm]
          using hsep ⟨a.val+1,by omega⟩ ⟨b.val+1,by omega⟩
      have h := ih (copyOne s) hs j
      rw [he] at h
      have haddr : (copyOne s).ptrs 34+(j.val:ℤ) = s.ptrs 34+(i.val:ℤ) := by
        rw [copyOne_src]; dsimp [j]; omega
      rw [haddr] at h
      have hne : s.ptrs 34+(i.val:ℤ) ≠ s.ptrs 35 := by
        simpa using hsep i ⟨0,by omega⟩
      simpa only [run,copyOne,Function.update_of_ne hne] using h

def setupOps : List Op :=
  [.pointerCopy 34 3, .pointerCopy 35 4, .pointerCopy 36 6,
   .pointerDec 36, .pointerConst 37 0]
def setup (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 34 (s.ptrs 3)) 35 (s.ptrs 4))
    36 (s.ptrs 6-1)) 37 0

def copyCmd : Cmd := .seq (opsCmd setupOps) (.whileDo (.pointerLE 37 36) body)
def copyEval (q : ℕ) (s : Store) : Store := run q (setup s)

lemma setup_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d (opsCmd setupOps) s (setup s) 5 := by
  simpa [setupOps,evalOps,Op.eval,setup,setPtr,Function.update_idem] using
    ops_exec d setupOps s

lemma copy_exec {N : ℕ} (d : Point N → Point N → ℝ) (q : ℕ) (s : Store)
    (hq : s.ptrs 6 = (q:ℤ)) :
    Executes d copyCmd s (copyEval q s) (7*q+7) := by
  have loop : ∀ (r : ℕ) (t : Store), t.ptrs 37+(r:ℤ)-1 = t.ptrs 36 →
      Executes d (.whileDo (.pointerLE 37 36) body) t (run r t) (7*r+2) := by
    intro r
    induction r with
    | zero =>
      intro t ht
      apply Executes.while_false
      simp only [Cond.test]; omega
    | succ r ih =>
      intro t ht
      have hg : (Cond.pointerLE 37 36).test t := by simp only [Cond.test]; omega
      have hr := ih (copyOne t) (by
        rw [copyOne_index,copyOne_ptr_frame t 36 (by decide) (by decide) (by decide) (by decide)]
        push_cast at ht; omega)
      have h := Executes.while_true hg (body_exec d t) hr
      simpa only [run,show 1+5+1+(7*r+2)=7*(r+1)+2 by omega] using h
  have hl := loop q (setup s) (by simp [setup,setPtr,hq])
  convert Executes.seq (setup_exec d s) hl using 1 <;> try rfl
  omega

lemma copy_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([34,35,36,37,38] : List ℕ)) : (copyEval q s).ptrs j = s.ptrs j := by
  have h34 : j ≠ 34 := by simp_all
  have h35 : j ≠ 35 := by simp_all
  have h36 : j ≠ 36 := by simp_all
  have h37 : j ≠ 37 := by simp_all
  have h38 : j ≠ 38 := by simp_all
  rw [copyEval,run_ptr_frame q (setup s) j h34 h35 h37 h38]
  simp [setup,setPtr,h34,h35,h36,h37]
lemma copy_frame (q : ℕ) (s : Store) : DataFrame s (copyEval q s) :=
  (show DataFrame s (setup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans (run_frame q (setup s))
lemma copy_dst (q : ℕ) (s : Store) : (copyEval q s).ptrs 35 = s.ptrs 4+(q:ℤ) := by
  rw [copyEval,run_dst]; simp [setup,setPtr]
lemma copy_memory_frame (q : ℕ) (s : Store) (x : ℤ)
    (hx : x < s.ptrs 4 ∨ s.ptrs 4+(q:ℤ) ≤ x) :
    (copyEval q s).imem x = s.imem x := by
  exact run_memory_frame q (setup s) x (by simpa [setup,setPtr] using hx)
lemma copy_memory_get (q : ℕ) (s : Store)
    (hsep : ∀ i j : Fin q, s.ptrs 3+(i.val:ℤ) ≠ s.ptrs 4+(j.val:ℤ))
    (i : Fin q) : (copyEval q s).imem (s.ptrs 4+(i.val:ℤ)) =
      s.imem (s.ptrs 3+(i.val:ℤ)) := by
  exact run_memory_get q (setup s) (by simpa [setup,setPtr] using hsep) i

lemma copyCmd_size : copyCmd.size = 13 := by decide

end StableMSR.Recovery.Compiler.ArrayCopy

set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.TableAppend
open ComponentMachine ArrayCopy

/- Locate the first free record using only additions, before copying its key. -/
def seekOps : List Op :=
  [.pointerCopy 4 2, .pointerCopy 39 6, .pointerInc 39,
   .pointerCopy 40 5, .pointerDec 40, .pointerConst 41 0]
def seekSetup (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 4 (s.ptrs 2)) 39 (s.ptrs 6+1))
    40 (s.ptrs 5-1)) 41 0

def seekBody : Cmd := opsCmd [.pointerAdd 4 4 39, .pointerInc 41]
def seekStep (s : Store) : Store :=
  setPtr (setPtr s 4 (s.ptrs 4+s.ptrs 39)) 41 (s.ptrs 41+1)
def seekCmd : Cmd := .seq (opsCmd seekOps) (.whileDo (.pointerLE 41 40) seekBody)
def seekEval (q : ℕ) (s : Store) : Store := seekStep^[q] (seekSetup s)

lemma seek_body_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d seekBody s (seekStep s) 2 := by
  simpa [seekBody,seekStep,evalOps,Op.eval,setPtr] using
    ops_exec d [.pointerAdd 4 4 39, .pointerInc 41] s
lemma seekStep_ptr_frame (s : Store) (j : ℕ) (h4 : j ≠ 4) (h41 : j ≠ 41) :
    (seekStep s).ptrs j = s.ptrs j := by simp [seekStep,setPtr,h4,h41]
lemma seekStep_index (s : Store) : (seekStep s).ptrs 41 = s.ptrs 41+1 := by
  simp [seekStep,setPtr]
lemma seekStep_cursor (q : ℕ) (s : Store) :
    (seekStep^[q] s).ptrs 4 = s.ptrs 4+(q:ℤ)*s.ptrs 39 := by
  induction q generalizing s with
  | zero => simp
  | succ q ih =>
    rw [Function.iterate_succ_apply,ih]
    simp [seekStep,setPtr,Nat.cast_add,Nat.cast_one]; ring
lemma seek_cursor (q : ℕ) (s : Store) :
    (seekEval q s).ptrs 4 = s.ptrs 2+(q:ℤ)*(s.ptrs 6+1) := by
  rw [seekEval,seekStep_cursor]; simp [seekSetup,setPtr]
lemma seek_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([4,39,40,41] : List ℕ)) : (seekEval q s).ptrs j = s.ptrs j := by
  have h4 : j ≠ 4 := by simp_all
  have h39 : j ≠ 39 := by simp_all
  have h40 : j ≠ 40 := by simp_all
  have h41 : j ≠ 41 := by simp_all
  rw [seekEval,iterate_preserves _ (fun t => t.ptrs j)
    (fun t => seekStep_ptr_frame t j h4 h41)]
  simp [seekSetup,setPtr,h4,h39,h40,h41]
lemma seek_imem (q : ℕ) (s : Store) : (seekEval q s).imem = s.imem := by
  exact iterate_preserves seekStep Store.imem (fun _ => rfl) q (seekSetup s)
lemma seek_frame (q : ℕ) (s : Store) : DataFrame s (seekEval q s) :=
  (show DataFrame s (seekSetup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame seekStep (fun _ => ⟨rfl,rfl,rfl,rfl,rfl⟩) q (seekSetup s))

lemma seek_exec {N : ℕ} (d : Point N → Point N → ℝ) (q : ℕ) (s : Store)
    (hq : s.ptrs 5 = (q:ℤ)) :
    Executes d seekCmd s (seekEval q s) (4*q+8) := by
  have hs : Executes d (opsCmd seekOps) s (seekSetup s) 6 := by
    simpa [seekOps,evalOps,Op.eval,seekSetup,setPtr,Function.update_idem] using
      ops_exec d seekOps s
  have hl := fixed_loop_exec d seekBody seekStep 41 40 2 (s.ptrs 5-1)
    (fun t _ => seek_body_exec d t) seekStep_index
    (fun t => seekStep_ptr_frame t 40 (by decide) (by decide)) q (seekSetup s)
    (by simp [seekSetup,setPtr]) (by simp [seekSetup,setPtr,hq])
  convert Executes.seq hs hl using 1 <;> try rfl
  omega

/- Append a payload after the newly copied key and increment the row count. -/
def finishCmd : Cmd := opsCmd [.integerStore 35 17, .pointerInc 5]
def finish (s : Store) : Store :=
  { s with
    imem := Function.update s.imem (s.ptrs 35) (s.ptrs 17)
    ptrs := Function.update s.ptrs 5 (s.ptrs 5+1) }
def appendCmd : Cmd := .seq seekCmd (.seq copyCmd finishCmd)
def appendEval (q L : ℕ) (s : Store) : Store := finish (copyEval L (seekEval q s))

lemma finish_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d finishCmd s (finish s) 2 := by
  simpa [finishCmd,finish,evalOps,Op.eval] using
    ops_exec d [.integerStore 35 17,.pointerInc 5] s
lemma append_exec {N : ℕ} (d : Point N → Point N → ℝ) (q L : ℕ) (s : Store)
    (hq : s.ptrs 5 = (q:ℤ)) (hL : s.ptrs 6 = (L:ℤ)) :
    Executes d appendCmd s (appendEval q L s) (4*q+7*L+17) := by
  have hL' : (seekEval q s).ptrs 6 = (L:ℤ) := by
    rw [seek_ptr_frame q s 6 (by simp),hL]
  have h := Executes.seq (seek_exec d q s hq)
    (Executes.seq (copy_exec d L (seekEval q s) hL') (finish_exec d _))
  convert h using 1 <;> try rfl
  omega

/- The start of record q for width L, a proof-side address abbreviation. -/
def endAddress (q L : ℕ) (s : Store) : ℤ := s.ptrs 2+(q:ℤ)*((L:ℤ)+1)
lemma copy_cursor (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) :
    (copyEval L (seekEval q s)).ptrs 35 = endAddress q L s+(L:ℤ) := by
  rw [copy_dst,seek_cursor,hL]; rfl
lemma append_memory (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) :
    (appendEval q L s).imem =
      Function.update (copyEval L (seekEval q s)).imem
        (endAddress q L s+(L:ℤ)) (s.ptrs 17) := by
  rw [appendEval,finish,copy_cursor q L s hL,
    copy_ptr_frame L (seekEval q s) 17 (by simp),seek_ptr_frame q s 17 (by simp)]
lemma append_ptr_frame (q L : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([4,5,34,35,36,37,38,39,40,41] : List ℕ)) :
    (appendEval q L s).ptrs j = s.ptrs j := by
  have h5 : j ≠ 5 := by simp_all
  change Function.update (copyEval L (seekEval q s)).ptrs 5 _ j = _
  rw [Function.update_of_ne h5,copy_ptr_frame,seek_ptr_frame] <;> simp_all
lemma append_count (q L : ℕ) (s : Store) :
    (appendEval q L s).ptrs 5 = s.ptrs 5+1 := by
  change (copyEval L (seekEval q s)).ptrs 5+1 = s.ptrs 5+1
  rw [copy_ptr_frame L (seekEval q s) 5 (by simp),seek_ptr_frame q s 5 (by simp)]
lemma append_frame (q L : ℕ) (s : Store) : DataFrame s (appendEval q L s) :=
  ((seek_frame q s).trans (copy_frame L (seekEval q s))).trans
    (show DataFrame (copyEval L (seekEval q s)) (finish (copyEval L (seekEval q s)))
      from ⟨rfl,rfl,rfl,rfl,rfl⟩)

lemma append_memory_frame (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (x : ℤ) (hx : x < endAddress q L s ∨ endAddress q L s+(L:ℤ)+1 ≤ x) :
    (appendEval q L s).imem x = s.imem x := by
  rw [append_memory q L s hL,Function.update_of_ne (show x ≠ endAddress q L s+(L:ℤ) by omega)]
  rw [copy_memory_frame L (seekEval q s) x,seek_imem]
  rw [seek_cursor,hL]
  change x < endAddress q L s ∨ endAddress q L s+(L:ℤ) ≤ x
  omega

lemma outside_interval (base x : ℤ) (L : ℕ)
    (h : ∀ i : Fin L, x ≠ base+(i.val:ℤ)) : x < base ∨ base+(L:ℤ) ≤ x := by
  by_contra hn
  have hnonneg : 0 ≤ x-base := by omega
  have hlt : (x-base).toNat < L := by omega
  exact h ⟨(x-base).toNat,hlt⟩ (by simp only [Int.toNat_of_nonneg hnonneg]; omega)

lemma append_key (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (hsep : ∀ i : Fin L, ∀ j : Fin (L+1),
      s.ptrs 3+(i.val:ℤ) ≠ endAddress q L s+(j.val:ℤ)) (i : Fin L) :
    (appendEval q L s).imem (endAddress q L s+(i.val:ℤ)) =
      s.imem (s.ptrs 3+(i.val:ℤ)) := by
  rw [append_memory q L s hL]
  have hne : endAddress q L s+(i.val:ℤ) ≠ endAddress q L s+(L:ℤ) := by
    have := i.isLt; omega
  rw [Function.update_of_ne hne]
  have hc := copy_memory_get L (seekEval q s) (by
    intro a b
    rw [seek_ptr_frame q s 3 (by simp),seek_cursor,hL]
    exact hsep a ⟨b.val,by omega⟩) i
  simpa only [seek_ptr_frame q s 3 (by simp),seek_cursor,hL,seek_imem,endAddress] using hc
lemma append_payload (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) :
    (appendEval q L s).imem (endAddress q L s+(L:ℤ)) = s.ptrs 17 := by
  rw [append_memory q L s hL]; simp
lemma append_query (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (hsep : ∀ i : Fin L, ∀ j : Fin (L+1),
      s.ptrs 3+(i.val:ℤ) ≠ endAddress q L s+(j.val:ℤ)) (i : Fin L) :
    (appendEval q L s).imem (s.ptrs 3+(i.val:ℤ)) =
      s.imem (s.ptrs 3+(i.val:ℤ)) := by
  apply append_memory_frame q L s hL
  have h := outside_interval (endAddress q L s) (s.ptrs 3+(i.val:ℤ)) (L+1) (hsep i)
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using h

lemma append_old_record (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (i : Fin q) (j : Fin (L+1)) :
    (appendEval q L s).imem
      (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) =
      s.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) := by
  apply append_memory_frame q L s hL
  left
  have hi : (i.val:ℤ)+1 ≤ (q:ℤ) := by have := i.isLt; omega
  have hj : (j.val:ℤ) < (L:ℤ)+1 := by have := j.isLt; omega
  have hp : 0 < (L:ℤ)+1 := by omega
  dsimp [endAddress]
  nlinarith

lemma appendCmd_size : appendCmd.size = 26 := by decide
noncomputable def program : MinSumFPT.Program := compile appendCmd 0
lemma program_length : program.length = 27 := by
  simp [program,compile,compileAt_length,appendCmd_size]
lemma append_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (q L : ℕ) (s : Store) (hq : s.ptrs 5 = (q:ℤ)) (hL : s.ptrs 6 = (L:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[4*q+7*L+18] (s.state 0 work) =
      (appendEval q L s).haltedState 26 (work+(4*q+7*L+18)) 0 := by
  simpa [program,appendCmd_size,Nat.add_assoc] using
    compile_halts (append_exec d q L s hq hL) ω work 0

end StableMSR.Recovery.Compiler.TableAppend

set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.TableAppend

/- A single fixed program constructs a new key/payload record in the next
free table slot, protects prior records, and advances the row count. -/
end StableMSR.Recovery.Compiler.TableAppend

open StableMSR.Recovery.Compiler.TableAppend
theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 27 ∧
    ∀ (N q L : ℕ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 5 = (q:ℤ) → s.ptrs 6 = (L:ℤ) →
      (∀ i : Fin L, ∀ j : Fin (L+1), s.ptrs 3+(i.val:ℤ) ≠
        s.ptrs 2+(q:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let base := s.ptrs 2+(q:ℤ)*((L:ℤ)+1)
      let result := (MinSumFPT.step P d ω)^[4*q+7*L+18] (s.state 0 work)
      result.halted = true ∧ result.work = work+(4*q+7*L+18) ∧
      result.cfg.ptrs 5 = ((q+1:ℕ):ℤ) ∧
      (∀ i : Fin L, result.imem (base+(i.val:ℤ)) = s.imem (s.ptrs 3+(i.val:ℤ))) ∧
      result.imem (base+(L:ℤ)) = s.ptrs 17 ∧
      (∀ i : Fin q, ∀ j : Fin (L+1),
        result.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ x : ℤ, x < base ∨ base+(L:ℤ)+1 ≤ x → result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∉ ([4,5,34,35,36,37,38,39,40,41] : List ℕ) →
        result.cfg.ptrs j = s.ptrs j) := by
  refine ⟨program,compile_deterministic appendCmd 0,program_length,?_⟩
  intro N q L d s hq hL hsep ω work
  dsimp only
  rw [append_machine_execution d q L s hq hL ω work]
  have hf := append_frame q L s
  refine ⟨rfl,rfl,?_,append_key q L s hL hsep,append_payload q L s hL,
    append_old_record q L s hL,append_memory_frame q L s hL,
    hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,append_ptr_frame q L s⟩
  change (appendEval q L s).ptrs 5 = _
  rw [append_count,hq]
  push_cast
  rfl

