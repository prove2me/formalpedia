-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.BitmapStats.bitmap_statistics_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T21:01:40.620068+00:00
-- url     : https://prove2.me/submissions/4c5a9df5-3080-4b44-8e19-f9e199b56253

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



namespace StableMSR.Recovery.BitmapStatsSemantics

variable {n : ℕ}

/- Whether the ordinary zero-based index is marked. -/
def marked (C : Finset (Fin n)) (i : ℕ) : Prop := ∃ v ∈ C, v.val = i

instance (C : Finset (Fin n)) (i : ℕ) : Decidable (marked C i) :=
  inferInstanceAs (Decidable (∃ v ∈ C, v.val = i))

@[simp] theorem marked_iff_mem (C : Finset (Fin n)) (v : Fin n) :
    marked C v.val ↔ v ∈ C := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact (Fin.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem bitmap_positive_iff {mem : ℤ → ℤ} {base : ℤ} {C : Finset (Fin n)}
    (hbitmap : ComponentMemory.Bitmap mem base C) (k : ℕ) (hk : k < n) :
    0 < mem (base + (k : ℤ)) ↔ marked C k := by
  have h := hbitmap ⟨k,hk⟩
  change mem (base + (k : ℤ)) = _ at h
  rw [h]
  have hm : marked C k ↔ (⟨k,hk⟩ : Fin n) ∈ C := marked_iff_mem C ⟨k,hk⟩
  rw [hm]
  split <;> simp_all

/- Scan positions k-1,...,0, adding one per mark and overwriting the minimum.
The incoming minimum is at least k. -/
def scan (C : Finset (Fin n)) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, count, minimum => (count, minimum)
  | k + 1, count, minimum =>
    if marked C k then scan C k (count + 1) k else scan C k count minimum

def below (C : Finset (Fin n)) (k : ℕ) : Finset (Fin n) :=
  C.filter (fun v => v.val < k)

@[simp] theorem mem_below (C : Finset (Fin n)) (k : ℕ) (v : Fin n) :
    v ∈ below C k ↔ v ∈ C ∧ v.val < k := Finset.mem_filter

theorem below_succ_marked (C : Finset (Fin n)) (k : ℕ) {v : Fin n}
    (hv : v ∈ C) (hval : v.val = k) :
    below C (k + 1) = insert v (below C k) := by
  ext w
  simp only [mem_below, Finset.mem_insert]
  constructor
  · rintro ⟨hw, hlt⟩
    by_cases he : w.val = k
    · exact Or.inl (Fin.ext (he.trans hval.symm))
    · exact Or.inr ⟨hw, by omega⟩
  · rintro (rfl | ⟨hw, hlt⟩)
    · exact ⟨hv, by omega⟩
    · exact ⟨hw, by omega⟩

theorem below_succ_unmarked (C : Finset (Fin n)) (k : ℕ)
    (h : ¬ marked C k) : below C (k + 1) = below C k := by
  ext v
  simp only [mem_below]
  constructor
  · rintro ⟨hv, hlt⟩
    exact ⟨hv, by have hn : v.val ≠ k := fun he => h ⟨v,hv,he⟩; omega⟩
  · rintro ⟨hv, hlt⟩
    exact ⟨hv, by omega⟩

/- Complete invariant of the descending scan: exact count, all lower bounds,
and either the incoming sentinel or a genuinely marked index. -/
theorem scan_spec (C : Finset (Fin n)) (k count minimum : ℕ)
    (hb : k ≤ minimum) :
    (scan C k count minimum).1 = count + (below C k).card ∧
    (scan C k count minimum).2 ≤ minimum ∧
    (∀ v ∈ below C k, (scan C k count minimum).2 ≤ v.val) ∧
    ((scan C k count minimum).2 = minimum ∨
      ∃ v ∈ below C k, (scan C k count minimum).2 = v.val) := by
  induction k generalizing count minimum with
  | zero => simp [scan, below]
  | succ k ih =>
    by_cases hm : marked C k
    · obtain ⟨v,hv,hval⟩ := hm
      have ih' := ih (count+1) k (by omega)
      have hbelow := below_succ_marked C k hv hval
      have hn : v ∉ below C k := by simp [hval]
      simp only [scan, if_pos (show marked C k from ⟨v,hv,hval⟩)]
      refine ⟨?_, ih'.2.1.trans (by omega), ?_, ?_⟩
      · rw [hbelow, Finset.card_insert_of_notMem hn, ih'.1]
        omega
      · intro w hw
        rw [hbelow] at hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simpa [hval] using ih'.2.1
        · exact ih'.2.2.1 w hw
      · rcases ih'.2.2.2 with he | ⟨w,hw,he⟩
        · exact Or.inr ⟨v, by rw [hbelow]; exact Finset.mem_insert_self _ _, he.trans hval.symm⟩
        · exact Or.inr ⟨w, by rw [hbelow]; exact Finset.mem_insert_of_mem hw, he⟩
    · simpa only [scan, if_neg hm, below_succ_unmarked C k hm]
        using ih count minimum (by omega)

@[simp] theorem below_all (C : Finset (Fin n)) : below C n = C := by
  ext v
  simp [v.isLt]

/- The least marked index; n is the sentinel precisely for an empty bitmap. -/
def least (C : Finset (Fin n)) : ℕ :=
  if h : C.Nonempty then (C.min' h).val else n

theorem scan_all_count (C : Finset (Fin n)) : (scan C n 0 n).1 = C.card := by
  simpa using (scan_spec C n 0 n (by omega)).1

theorem scan_all_least (C : Finset (Fin n)) : (scan C n 0 n).2 = least C := by
  have hs := scan_spec C n 0 n (by omega)
  simp only [below_all] at hs
  by_cases h : C.Nonempty
  · obtain ⟨v,hv⟩ := h
    have hn : (scan C n 0 n).2 ≠ n := by
      have := hs.2.2.1 v hv
      have := v.isLt
      omega
    obtain ⟨w,hw,he⟩ := hs.2.2.2.resolve_left hn
    have hlo : ((C.min' ⟨v,hv⟩).val) ≤ (scan C n 0 n).2 := by
      rw [he]
      exact Finset.min'_le C w hw
    have hhi := hs.2.2.1 (C.min' ⟨v,hv⟩) (Finset.min'_mem C ⟨v,hv⟩)
    simp only [least, dif_pos (show C.Nonempty from ⟨v,hv⟩)]
    exact Nat.le_antisymm hhi hlo
  · simp only [least, dif_neg h]
    rcases hs.2.2.2 with he | ⟨v,hv,_⟩
    · exact he
    · exact (h ⟨v,hv⟩).elim

theorem scan_all (C : Finset (Fin n)) : scan C n 0 n = (C.card, least C) :=
  Prod.ext (scan_all_count C) (scan_all_least C)

theorem least_eq_sentinel_iff (C : Finset (Fin n)) : least C = n ↔ C = ∅ := by
  by_cases h : C.Nonempty
  · have hlt : least C < n := by simp [least, h, (C.min' h).isLt]
    constructor
    · intro he; omega
    · intro he; exact (h.ne_empty he).elim
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [least, h, he]

theorem least_mem_and_le (C : Finset (Fin n)) (h : C.Nonempty) :
    (∃ v ∈ C, v.val = least C) ∧ ∀ v ∈ C, least C ≤ v.val := by
  simp only [least, dif_pos h]
  exact ⟨⟨C.min' h, Finset.min'_mem C h, rfl⟩, fun v hv => Finset.min'_le C v hv⟩

end StableMSR.Recovery.BitmapStatsSemantics


set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.BitmapStats

open ComponentMachine

def prepOps : List Op :=
  [.pointerConst 0 0, .pointerConst 18 0, .pointerCopy 19 6,
    .pointerCopy 20 6, .pointerDec 20]

def prepEval (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 0 0) 18 0) 19 (s.ptrs 6)) 20 (s.ptrs 6 - 1)

def pad3 : Cmd := .seq nop pad2

def selectCmd : Cmd :=
  .ite (.pointerLE 22 0) pad3 (opsCmd [.pointerInc 18, .pointerCopy 19 20])

def selectEval (s : Store) : Store :=
  if s.ptrs 22 ≤ s.ptrs 0 then s else setPtr (incPtr s 18) 19 (s.ptrs 20)

def body : Cmd :=
  .seq (opsCmd [.pointerAdd 21 3 20, .integerLoad 22 21])
    (.seq selectCmd (.atom (.pointerDec 20)))

def inputEval (s : Store) : Store :=
  setPtr (setPtr s 21 (s.ptrs 3 + s.ptrs 20)) 22 (s.imem (s.ptrs 3 + s.ptrs 20))

def step (s : Store) : Store :=
  let t := selectEval (inputEval s)
  setPtr t 20 (t.ptrs 20 - 1)

def run : ℕ → Store → Store
  | 0, s => s
  | q+1, s => run q (step s)

def loop : Cmd := .whileDo (.pointerLE 0 20) body

def statsCmd : Cmd := .seq (opsCmd prepOps) loop

def statsEval (q : ℕ) (s : Store) : Store := run q (prepEval s)

@[simp] lemma statsCmd_size : statsCmd.size = 18 := rfl

lemma prep_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d (opsCmd prepOps) s (prepEval s) 5 := by
  simpa [prepOps,evalOps,prepEval,Op.eval,setPtr,Function.update_idem] using
    ops_exec d prepOps s

lemma select_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d selectCmd s (selectEval s) 4 := by
  by_cases h : s.ptrs 22 ≤ s.ptrs 0
  · have hp : Executes d pad3 s s 3 := Executes.seq (nop_exec d s) (pad2_exec d s)
    simpa [selectCmd,selectEval,h] using
      Executes.ite_true (c := Cond.pointerLE 22 0)
        (no := opsCmd [.pointerInc 18, .pointerCopy 19 20]) h hp
  · have hp := ops_exec d [.pointerInc 18, .pointerCopy 19 20] s
    simpa [selectCmd,selectEval,h,evalOps,Op.eval,incPtr,setPtr] using
      Executes.ite_false (c := Cond.pointerLE 22 0) (yes := pad3) h hp

lemma body_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d body s (step s) 7 := by
  have hi : Executes d (opsCmd [.pointerAdd 21 3 20, .integerLoad 22 21])
      s (inputEval s) 2 := by
    simpa [evalOps,Op.eval,inputEval,setPtr] using
      ops_exec d [.pointerAdd 21 3 20, .integerLoad 22 21] s
  exact Executes.seq hi (Executes.seq (select_exec d _)
    (Executes.atom (.pointerDec 20) _))

lemma step_ptr_frame (s : Store) (j : ℕ)
    (h18 : j ≠ 18) (h19 : j ≠ 19) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) :
    (step s).ptrs j = s.ptrs j := by
  simp only [step,selectEval]
  split <;> simp [setPtr,incPtr,inputEval,h18,h19,h20,h21,h22]

lemma step_index (s : Store) : (step s).ptrs 20 = s.ptrs 20 - 1 := by
  simp only [step,selectEval]
  split <;> simp [setPtr,incPtr,inputEval]

lemma step_count (s : Store) :
    (step s).ptrs 18 = if s.imem (s.ptrs 3+s.ptrs 20) ≤ s.ptrs 0
      then s.ptrs 18 else s.ptrs 18+1 := by
  simp only [step,selectEval]
  split <;> simp_all [setPtr,incPtr,inputEval]

lemma step_minimum (s : Store) :
    (step s).ptrs 19 = if s.imem (s.ptrs 3+s.ptrs 20) ≤ s.ptrs 0
      then s.ptrs 19 else s.ptrs 20 := by
  simp only [step,selectEval]
  split <;> simp_all [setPtr,incPtr,inputEval]

lemma step_frame (s : Store) :
    (step s).regs = s.regs ∧ (step s).mem = s.mem ∧ (step s).imem = s.imem ∧
    (step s).queries = s.queries ∧ (step s).tapePos = s.tapePos ∧
    (step s).output = s.output := by
  simp only [step,selectEval]
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

lemma run_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (h18 : j ≠ 18) (h19 : j ≠ 19) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) :
    (run q s).ptrs j = s.ptrs j := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => rw [run,ih,step_ptr_frame s j h18 h19 h20 h21 h22]

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
    Executes d loop s (run q s) (9*q+2) := by
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
    simpa only [loop,run,show 1+7+1+(9*q+2)=9*(q+1)+2 by omega] using he

lemma stats_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    Executes d statsCmd s (statsEval q s) (9*q+7) := by
  have hz : (prepEval s).ptrs 0 = 0 := by simp [prepEval,setPtr]
  have hi : (prepEval s).ptrs 20 = (q : ℤ)-1 := by simp [prepEval,setPtr,hcount]
  have h := Executes.seq (prep_exec d s) (loop_exec d q (prepEval s) hz hi)
  simpa only [statsCmd,statsEval,show 5+(9*q+2)=9*q+7 by omega] using h

lemma stats_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (h0 : j ≠ 0) (h18 : j ≠ 18) (h19 : j ≠ 19) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) :
    (statsEval q s).ptrs j = s.ptrs j := by
  rw [statsEval,run_ptr_frame q (prepEval s) j h18 h19 h20 h21 h22]
  simp [prepEval,setPtr,h0,h18,h19,h20]

lemma stats_frame (q : ℕ) (s : Store) :
    (statsEval q s).regs = s.regs ∧ (statsEval q s).mem = s.mem ∧
    (statsEval q s).imem = s.imem ∧ (statsEval q s).queries = s.queries ∧
    (statsEval q s).tapePos = s.tapePos ∧ (statsEval q s).output = s.output :=
  run_frame q (prepEval s)

end StableMSR.Recovery.Compiler.BitmapStats


set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.BitmapStats

open ComponentMachine ComponentMemory BitmapStatsSemantics

lemma run_stats {n : ℕ} (C : Finset (Fin n)) (q : ℕ) (s : Store)
    (count minimum : ℕ) (hq : q ≤ n) (hzero : s.ptrs 0 = 0)
    (hindex : s.ptrs 20 = (q : ℤ)-1)
    (hbitmap : Bitmap s.imem (s.ptrs 3) C)
    (hcount : s.ptrs 18 = (count : ℤ)) (hminimum : s.ptrs 19 = (minimum : ℤ)) :
    (run q s).ptrs 18 = ((scan C q count minimum).1 : ℤ) ∧
    (run q s).ptrs 19 = ((scan C q count minimum).2 : ℤ) := by
  induction q generalizing s count minimum with
  | zero => exact ⟨hcount,hminimum⟩
  | succ q ih =>
    let v : Fin n := ⟨q,by omega⟩
    have hv : marked C q ↔ v ∈ C := marked_iff_mem C v
    have hi : s.ptrs 20 = (q : ℤ) := by
      rw [hindex]
      push_cast
      omega
    have hcell : s.imem (s.ptrs 3+s.ptrs 20) = if v ∈ C then 1 else 0 := by
      rw [hi]
      exact hbitmap v
    have ht : s.imem (s.ptrs 3+s.ptrs 20) ≤ s.ptrs 0 ↔ ¬ marked C q := by
      rw [hcell,hzero,hv]
      by_cases hm : v ∈ C <;> simp [hm]
    have hz : (step s).ptrs 0 = 0 := by
      rw [step_ptr_frame s 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hzero
    have hb : Bitmap (step s).imem ((step s).ptrs 3) C := by
      rw [(step_frame s).2.2.1,
        step_ptr_frame s 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hbitmap
    have hnext : (step s).ptrs 20 = (q : ℤ)-1 := by rw [step_index,hi]
    by_cases hm : marked C q
    · have hn : ¬ (s.imem (s.ptrs 3+s.ptrs 20) ≤ s.ptrs 0) := by
        intro h
        exact ht.mp h hm
      have hc : (step s).ptrs 18 = ((count+1 : ℕ) : ℤ) := by
        rw [step_count,if_neg hn,hcount]
        push_cast
        rfl
      have hmin : (step s).ptrs 19 = (q : ℤ) := by rw [step_minimum,if_neg hn,hi]
      simpa only [run,scan,if_pos hm] using
        ih (step s) (count+1) q (by omega) hz hnext hb hc hmin
    · have hy := ht.mpr hm
      have hc : (step s).ptrs 18 = (count : ℤ) := by rw [step_count,if_pos hy,hcount]
      have hmin : (step s).ptrs 19 = (minimum : ℤ) := by
        rw [step_minimum,if_pos hy,hminimum]
      simpa only [run,scan,if_neg hm] using
        ih (step s) count minimum (by omega) hz hnext hb hc hmin

lemma stats_values {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C) :
    (statsEval n s).ptrs 18 = (C.card : ℤ) ∧
    (statsEval n s).ptrs 19 = (least C : ℤ) := by
  have hp : Bitmap (prepEval s).imem ((prepEval s).ptrs 3) C := by
    simpa [prepEval,setPtr] using hbitmap
  have h := run_stats C n (prepEval s) 0 n (le_refl _)
    (by simp [prepEval,setPtr]) (by simp [prepEval,setPtr,hcount]) hp
    (by simp [prepEval,setPtr]) (by simp [prepEval,setPtr,hcount])
  simpa only [statsEval,scan_all] using h

lemma stats_count {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C) :
    (statsEval n s).ptrs 18 = (C.card : ℤ) :=
  (stats_values s C hcount hbitmap).1

lemma stats_sentinel_iff {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C) :
    (statsEval n s).ptrs 19 = (n : ℤ) ↔ C = ∅ := by
  rw [(stats_values s C hcount hbitmap).2,Nat.cast_inj]
  exact least_eq_sentinel_iff C

lemma stats_minimum {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C)
    (hne : C.Nonempty) :
    ∃ v ∈ C, (statsEval n s).ptrs 19 = (v.val : ℤ) ∧
      ∀ u ∈ C, v.val ≤ u.val := by
  rcases least_mem_and_le C hne with ⟨⟨v,hv,he⟩,hmin⟩
  refine ⟨v,hv,?_,?_⟩
  · rw [(stats_values s C hcount hbitmap).2,he]
  · intro u hu
    rw [he]
    exact hmin u hu

lemma stats_minimum_bounds {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C) :
    0 ≤ (statsEval n s).ptrs 19 ∧ (statsEval n s).ptrs 19 ≤ (n : ℤ) := by
  rw [(stats_values s C hcount hbitmap).2]
  constructor
  · exact Nat.cast_nonneg _
  · apply Nat.cast_le.mpr
    by_cases h : C.Nonempty
    · simp only [least,dif_pos h]
      exact Nat.le_of_lt (C.min' h).isLt
    · simp [least,h]

/- One fixed deterministic program counts a bitmap and returns its least marked index. -/
end StableMSR.Recovery.Compiler.BitmapStats

open StableMSR.Recovery.Compiler.BitmapStats StableMSR.Recovery.ComponentMemory
theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 19 ∧
      ∀ (N n : ℕ) (d : Point N → Point N → ℝ) (ω : ℕ → ℝ)
        (s : Store) (C : Finset (Fin n)) (w : ℕ),
        s.ptrs 6 = (n : ℤ) → Bitmap s.imem (s.ptrs 3) C →
        ∃ t : Store,
          t.ptrs 18 = (C.card : ℤ) ∧
          (t.ptrs 19 = (n : ℤ) ↔ C = ∅) ∧
          (C.Nonempty → ∃ v ∈ C, t.ptrs 19 = (v.val : ℤ) ∧
            ∀ u ∈ C, v.val ≤ u.val) ∧
          (0 ≤ t.ptrs 19 ∧ t.ptrs 19 ≤ (n : ℤ)) ∧
          (∀ j : ℕ, j ≠ 0 → j ≠ 18 → j ≠ 19 → j ≠ 20 →
            j ≠ 21 → j ≠ 22 → t.ptrs j = s.ptrs j) ∧
          t.regs = s.regs ∧ t.mem = s.mem ∧ t.imem = s.imem ∧
          t.queries = s.queries ∧ t.tapePos = s.tapePos ∧ t.output = s.output ∧
          (MinSumFPT.step P d ω)^[9*n+8] (s.state 0 w) =
            t.haltedState 18 (w+(9*n+8)) 0 := by
  refine ⟨compile statsCmd 0,compile_deterministic statsCmd 0,?_,?_⟩
  · simp [compile]
  · intro N n d ω s C w hcount hbitmap
    refine ⟨statsEval n s,stats_count s C hcount hbitmap,
      stats_sentinel_iff s C hcount hbitmap,
      stats_minimum s C hcount hbitmap,stats_minimum_bounds s C hcount hbitmap,?_,?_⟩
    · intro j h0 h18 h19 h20 h21 h22
      exact stats_ptr_frame n s j h0 h18 h19 h20 h21 h22
    · rcases stats_frame n s with ⟨h1,h2,h3,h4,h5,h6⟩
      refine ⟨h1,h2,h3,h4,h5,h6,?_⟩
      have h := compile_halts (stats_exec d n s hcount) ω w 0
      simpa only [statsCmd_size,show 9*n+7+1=9*n+8 by omega,
        show w+(9*n+7)+1=w+(9*n+8) by omega] using h

