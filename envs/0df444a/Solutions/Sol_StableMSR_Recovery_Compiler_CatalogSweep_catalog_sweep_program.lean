-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.CatalogSweep.catalog_sweep_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-15T21:10:21.294582+00:00
-- url     : https://prove2.me/submissions/a9d69edc-1752-4dfe-8383-f2bd64700f8c

import Definitions.Def_StableMSR_ComponentGraphMemory
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler
namespace StableMSR.Recovery.Compiler
lemma compile_deterministic (cmd : Cmd) (result : ℕ) :
    DeterministicProgram (compile cmd result) := (compiler_execution_exact cmd result).1
lemma compile_halts {n : ℕ} {d : Point n → Point n → ℝ} {cmd : Cmd} {s t : Store}
    {cost : ℕ} (h : Executes d cmd s t cost) (ω : ℕ → ℝ) (w result : ℕ) :
    (MinSumFPT.step (compile cmd result) d ω)^[cost+1] (s.state 0 w) =
      t.haltedState cmd.size (w+cost+1) result :=
  (compiler_execution_exact cmd result).2 n d s t cost h ω w
@[simp] lemma compileAt_length (pc : ℕ) (cmd : Cmd) :
    (compileAt pc cmd).length = cmd.size := by
  induction cmd generalizing pc <;> simp_all [compileAt, Cmd.size] <;> omega
end StableMSR.Recovery.Compiler
namespace StableMSR.Recovery.Compiler.TupleWriter

/- Store a register at the output pointer and advance that pointer. -/
def writeOne (out r : ℕ) (s : Store) : Store :=
  { s with
    imem := Function.update s.imem (s.ptrs out) (s.ptrs r)
    ptrs := Function.update s.ptrs out (s.ptrs out+1) }

def writeRegs (out : ℕ) : List ℕ → Cmd
  | [] => .skip
  | r::rs => .seq (.atom (.integerStore out r))
      (.seq (.atom (.pointerInc out)) (writeRegs out rs))

@[simp] lemma writeRegs_size (out : ℕ) (rs : List ℕ) :
    (writeRegs out rs).size = 2*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [writeRegs,Cmd.size,List.length_cons,ih]; omega

def writeStore (out : ℕ) : List ℕ → Store → Store
  | [], s => s
  | r::rs, s => writeStore out rs (writeOne out r s)

/- Consecutive integer-memory writes, in stream order. -/
def writeMemory (base : ℤ) (values : List ℤ) (mem : ℤ → ℤ) : ℤ → ℤ :=
  match values with
  | [] => mem
  | v::vs => writeMemory (base+1) vs (Function.update mem base v)

@[simp] theorem writeMemory_nil (a : ℤ) (mem : ℤ → ℤ) : writeMemory a [] mem = mem := rfl

lemma writeMemory_append (a : ℤ) (xs ys : List ℤ) (mem : ℤ → ℤ) :
    writeMemory a (xs++ys) mem =
      writeMemory (a+(xs.length : ℤ)) ys (writeMemory a xs mem) := by
  induction xs generalizing a mem with
  | nil => simp [writeMemory]
  | cons x xs ih =>
    simp only [List.cons_append,writeMemory,List.length_cons]
    rw [ih]
    congr 1
    push_cast
    ring

lemma writeMemory_before (a x : ℤ) (values : List ℤ) (mem : ℤ → ℤ) (hx : x < a) :
    writeMemory a values mem x = mem x := by
  induction values generalizing a mem with
  | nil => rfl
  | cons v vs ih =>
    rw [writeMemory,ih (a+1) (Function.update mem a v) (by omega)]
    simp [show x ≠ a by omega]

lemma writeMemory_after (a x : ℤ) (values : List ℤ) (mem : ℤ → ℤ)
    (hx : a+(values.length : ℤ) ≤ x) :
    writeMemory a values mem x = mem x := by
  induction values generalizing a mem with
  | nil => rfl
  | cons v vs ih =>
    have hlen : ((v::vs).length : ℤ) = vs.length + 1 := by simp
    rw [writeMemory,ih (a+1) (Function.update mem a v) (by omega)]
    simp [show x ≠ a by have := Int.natCast_nonneg vs.length; omega]

lemma writeMemory_get (a : ℤ) (values : List ℤ) (mem : ℤ → ℤ)
    (i : ℕ) (hi : i < values.length) :
    writeMemory a values mem (a+(i : ℤ)) = values[i] := by
  induction values generalizing a mem i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero =>
      simp only [Nat.cast_zero,add_zero,List.getElem_cons_zero,writeMemory]
      rw [writeMemory_before (a+1) a vs (Function.update mem a v) (by omega)]
      simp
    | succ i =>
      have hi' : i < vs.length := by simpa using hi
      have he : a+((i+1 : ℕ) : ℤ) = (a+1)+(i : ℤ) := by push_cast; ring
      rw [writeMemory,he,ih (a+1) (Function.update mem a v) i hi']
      rfl

lemma writeRegs_exec {n : ℕ} (d : Point n → Point n → ℝ)
    (out : ℕ) (rs : List ℕ) (s : Store) :
    Executes d (writeRegs out rs) s (writeStore out rs s) (2*rs.length) := by
  induction rs generalizing s with
  | nil => exact Executes.skip s
  | cons r rs ih =>
    have he := Executes.seq (Executes.atom (.integerStore out r) s)
      (Executes.seq (Executes.atom (.pointerInc out) ((Op.integerStore out r).eval d s))
        (ih (writeOne out r s)))
    simpa only [writeRegs,writeStore,List.length_cons,
      show 2*(rs.length+1) = 1+(1+2*rs.length) by omega] using he

@[simp] lemma writeOne_ptr_out (out r : ℕ) (s : Store) :
    (writeOne out r s).ptrs out = s.ptrs out+1 := by simp [writeOne]
lemma writeOne_ptr_ne (out r j : ℕ) (s : Store) (hj : j ≠ out) :
    (writeOne out r s).ptrs j = s.ptrs j := by simp [writeOne,hj]

lemma writeStore_ptr_out (out : ℕ) (rs : List ℕ) (s : Store) :
    (writeStore out rs s).ptrs out = s.ptrs out+(rs.length : ℤ) := by
  induction rs generalizing s with
  | nil => simp [writeStore]
  | cons r rs ih =>
    simp only [writeStore,ih,writeOne_ptr_out,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring
lemma writeStore_ptr_ne (out j : ℕ) (rs : List ℕ) (s : Store) (hj : j ≠ out) :
    (writeStore out rs s).ptrs j = s.ptrs j := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => rw [writeStore,ih,writeOne_ptr_ne out r j s hj]

lemma writeStore_frame (out : ℕ) (rs : List ℕ) (s : Store) :
    (writeStore out rs s).regs = s.regs ∧
    (writeStore out rs s).mem = s.mem ∧
    (writeStore out rs s).queries = s.queries ∧
    (writeStore out rs s).tapePos = s.tapePos ∧
    (writeStore out rs s).output = s.output := by
  induction rs generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons r rs ih => exact ih (writeOne out r s)

lemma writeStore_memory (out : ℕ) (rs : List ℕ) (s : Store) (hf : out ∉ rs) :
    (writeStore out rs s).imem = writeMemory (s.ptrs out) (rs.map s.ptrs) s.imem := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    have hr : r ≠ out := by simp only [List.mem_cons,not_or] at hf; exact Ne.symm hf.1
    have hrs : out ∉ rs := by simp only [List.mem_cons,not_or] at hf; exact hf.2
    rw [writeStore,ih (writeOne out r s) hrs]
    have hm : rs.map (writeOne out r s).ptrs = rs.map s.ptrs := by
      apply List.map_congr_left
      intro j hj
      exact writeOne_ptr_ne out r j s (fun he => hrs (he ▸ hj))
    simp only [hm,writeOne_ptr_out,List.map_cons,writeMemory]
    rfl

/- A fixed-width output record: header followed by the digit registers. -/
def writerRegs (w : ℕ) : List ℕ := (w+2)::((List.range w).map (·+1))
def writer (w : ℕ) : Cmd := writeRegs (w+1) (writerRegs w)
def writerEval (w : ℕ) (s : Store) : Store := writeStore (w+1) (writerRegs w) s

@[simp] lemma writerRegs_length (w : ℕ) : (writerRegs w).length = w+1 := by simp [writerRegs]
@[simp] lemma writer_size (w : ℕ) : (writer w).size = 2*(w+1) := by
  simp [writer]
lemma writerRegs_fresh (w : ℕ) : w+1 ∉ writerRegs w := by
  simp only [writerRegs,List.mem_cons,List.mem_map,List.mem_range]
  rintro (he | ⟨i,hi,he⟩) <;> omega
lemma writer_exec {n : ℕ} (d : Point n → Point n → ℝ) (w : ℕ) (s : Store) :
    Executes d (writer w) s (writerEval w s) (2*(w+1)) := by
  simpa [writer,writerEval] using writeRegs_exec d (w+1) (writerRegs w) s
lemma writer_ptr_out (w : ℕ) (s : Store) :
    (writerEval w s).ptrs (w+1) = s.ptrs (w+1)+(w+1 : ℕ) := by
  simp [writerEval,writeStore_ptr_out]
lemma writer_ptr_ne (w j : ℕ) (s : Store) (hj : j ≠ w+1) :
    (writerEval w s).ptrs j = s.ptrs j := writeStore_ptr_ne (w+1) j (writerRegs w) s hj
lemma writer_frame (w : ℕ) (s : Store) :
    (writerEval w s).regs = s.regs ∧ (writerEval w s).mem = s.mem ∧
    (writerEval w s).queries = s.queries ∧ (writerEval w s).tapePos = s.tapePos ∧
    (writerEval w s).output = s.output := writeStore_frame (w+1) (writerRegs w) s
lemma writer_memory (w : ℕ) (s : Store) :
    (writerEval w s).imem =
      writeMemory (s.ptrs (w+1)) ((writerRegs w).map s.ptrs) s.imem :=
  writeStore_memory (w+1) (writerRegs w) s (writerRegs_fresh w)

lemma writer_header (w : ℕ) (s : Store) (hw : s.ptrs (w+2) = (w : ℤ)) :
    (writerEval w s).imem (s.ptrs (w+1)) = (w : ℤ) := by
  rw [writer_memory]
  have h := writeMemory_get (s.ptrs (w+1)) ((writerRegs w).map s.ptrs) s.imem 0 (by simp)
  simpa [writerRegs,hw] using h

lemma writer_digit (w : ℕ) (s : Store) (i : ℕ) (hi : i < w) :
    (writerEval w s).imem (s.ptrs (w+1)+1+(i : ℤ)) = s.ptrs (i+1) := by
  rw [writer_memory]
  have h := writeMemory_get (s.ptrs (w+1)) ((writerRegs w).map s.ptrs) s.imem (i+1) (by simp; omega)
  simpa [writerRegs,List.getElem_map,List.getElem_range,hi,add_assoc,add_comm,add_left_comm] using h

lemma writer_before (w : ℕ) (s : Store) (x : ℤ) (hx : x < s.ptrs (w+1)) :
    (writerEval w s).imem x = s.imem x := by
  rw [writer_memory]
  exact writeMemory_before _ _ _ _ hx

lemma writer_after (w : ℕ) (s : Store) (x : ℤ)
    (hx : s.ptrs (w+1)+(w+1 : ℕ) ≤ x) :
    (writerEval w s).imem x = s.imem x := by
  rw [writer_memory]
  apply writeMemory_after
  simpa using hx

end StableMSR.Recovery.Compiler.TupleWriter

namespace StableMSR.Recovery.Compiler.BitmapFill

open TupleWriter

/- One iteration of an integer-array fill. -/
def fillBody (out value : ℕ) : Cmd :=
  .seq (.atom (.integerStore out value)) (.atom (.pointerInc out))

/- A fixed program whose input stop pointer determines the fill length. -/
def fillCmd (out stop value : ℕ) : Cmd :=
  .whileDo (.pointerLE out stop) (fillBody out value)

@[simp] lemma fillBody_size (out value : ℕ) : (fillBody out value).size = 2 := rfl

@[simp] lemma fillCmd_size (out stop value : ℕ) : (fillCmd out stop value).size = 5 := rfl

/- Mathematical effect of filling `q` consecutive cells. -/
def fillEval (out value q : ℕ) (s : Store) : Store :=
  writeStore out (List.replicate q value) s

@[simp] lemma fillEval_zero (out value : ℕ) (s : Store) :
    fillEval out value 0 s = s := rfl

lemma fillEval_succ (out value q : ℕ) (s : Store) :
    fillEval out value (q+1) s = fillEval out value q (writeOne out value s) := by
  simp only [fillEval,List.replicate_succ,writeStore]

lemma fillBody_exec {n : ℕ} (d : Point n → Point n → ℝ)
    (out value : ℕ) (s : Store) :
    Executes d (fillBody out value) s (writeOne out value s) 2 := by
  exact Executes.seq (Executes.atom (.integerStore out value) s)
    (Executes.atom (.pointerInc out) ((.integerStore out value : Op).eval d s))

/- Exact execution cost includes the final unsuccessful loop test. -/
lemma fill_exec {n : ℕ} (d : Point n → Point n → ℝ)
    (out stop value q : ℕ) (s : Store) (hne : out ≠ stop)
    (hstop : s.ptrs stop = s.ptrs out + (q : ℤ) - 1) :
    Executes d (fillCmd out stop value) s (fillEval out value q s) (4*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test]
    simp only [Nat.cast_zero] at hstop
    omega
  | succ q ih =>
    have hguard : (Cond.pointerLE out stop).test s := by
      simp only [Cond.test]
      simp only [Nat.cast_add,Nat.cast_one] at hstop
      omega
    have hnext : (writeOne out value s).ptrs stop =
        (writeOne out value s).ptrs out + (q : ℤ) - 1 := by
      rw [writeOne_ptr_ne out value stop s (Ne.symm hne),writeOne_ptr_out]
      simp only [Nat.cast_add,Nat.cast_one] at hstop
      omega
    have hex := Executes.while_true hguard (fillBody_exec d out value s)
      (ih (writeOne out value s) hnext)
    simpa only [fillCmd,fillEval_succ,show 1+2+1+(4*q+2) = 4*(q+1)+2 by omega]
      using hex

lemma fill_ptr_out (out value q : ℕ) (s : Store) :
    (fillEval out value q s).ptrs out = s.ptrs out + (q : ℤ) := by
  simpa only [fillEval,List.length_replicate] using
    writeStore_ptr_out out (List.replicate q value) s

lemma fill_ptr_ne (out value q j : ℕ) (s : Store) (hj : j ≠ out) :
    (fillEval out value q s).ptrs j = s.ptrs j :=
  writeStore_ptr_ne out j (List.replicate q value) s hj

lemma fill_frame (out value q : ℕ) (s : Store) :
    (fillEval out value q s).regs = s.regs ∧
    (fillEval out value q s).mem = s.mem ∧
    (fillEval out value q s).queries = s.queries ∧
    (fillEval out value q s).tapePos = s.tapePos ∧
    (fillEval out value q s).output = s.output :=
  writeStore_frame out (List.replicate q value) s

lemma fill_memory (out value q : ℕ) (s : Store) (hne : out ≠ value) :
    (fillEval out value q s).imem =
      writeMemory (s.ptrs out) (List.replicate q (s.ptrs value)) s.imem := by
  have hf : out ∉ List.replicate q value := by simp [hne]
  simpa only [fillEval,List.map_replicate] using
    writeStore_memory out (List.replicate q value) s hf

lemma fill_memory_get (out value q i : ℕ) (s : Store)
    (hne : out ≠ value) (hi : i < q) :
    (fillEval out value q s).imem (s.ptrs out + (i : ℤ)) = s.ptrs value := by
  rw [fill_memory out value q s hne]
  have hi' : i < (List.replicate q (s.ptrs value)).length := by simpa using hi
  rw [writeMemory_get _ _ _ i hi']
  simp

lemma fill_memory_before (out value q : ℕ) (s : Store) (x : ℤ)
    (hne : out ≠ value) (hx : x < s.ptrs out) :
    (fillEval out value q s).imem x = s.imem x := by
  rw [fill_memory out value q s hne]
  exact writeMemory_before _ _ _ _ hx

lemma fill_memory_after (out value q : ℕ) (s : Store) (x : ℤ)
    (hne : out ≠ value) (hx : s.ptrs out + (q : ℤ) ≤ x) :
    (fillEval out value q s).imem x = s.imem x := by
  rw [fill_memory out value q s hne]
  apply writeMemory_after
  simpa only [List.length_replicate] using hx

end StableMSR.Recovery.Compiler.BitmapFill

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

namespace StableMSR.Recovery.Compiler.ComponentInit
def prepCmd : Cmd :=
  .seq (.atom (.pointerConst 0 0))
    (.seq (.atom (.pointerConst 1 1))
      (.seq (.atom (.pointerCopy 15 4))
        (.seq (.atom (.pointerAdd 16 4 6)) (.atom (.pointerDec 16)))))

def prepEval (s : Store) : Store :=
  { s with ptrs := (Function.update
      (Function.update (Function.update (Function.update s.ptrs 0 0) 1 1) 15 (s.ptrs 4))
      16 (s.ptrs 4 + s.ptrs 6 - 1)) }

lemma prep_exec {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    Executes d prepCmd s (prepEval s) 5 := by
  have h := Executes.seq (Executes.atom (.pointerConst 0 0) (d := d) s)
    (Executes.seq (Executes.atom (.pointerConst 1 1) (d := d) _)
      (Executes.seq (Executes.atom (.pointerCopy 15 4) (d := d) _)
        (Executes.seq (Executes.atom (.pointerAdd 16 4 6) (d := d) _)
          (Executes.atom (.pointerDec 16) (d := d) _))))
  simpa [prepCmd,prepEval,Op.eval,Function.update_idem] using h

end StableMSR.Recovery.Compiler.ComponentInit

namespace StableMSR.Recovery.Compiler.BoundaryProgram
open ComponentInit ComponentMachine BitmapFill ComponentMemory
def clearCmd : Cmd := .seq prepCmd (fillCmd 15 16 0)
def clearEval (n : ℕ) (s : Store) : Store := fillEval 15 0 n (prepEval s)

lemma clear_exec {N : ℕ} (d : Point N → Point N → ℝ) (n : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d clearCmd s (clearEval n s) (4*n+7) := by
  have hs : (prepEval s).ptrs 16 = (prepEval s).ptrs 15+(n:ℤ)-1 := by
    simp [prepEval,hn]
  have h := Executes.seq (prep_exec d s)
    (fill_exec d 15 16 0 n (prepEval s) (by decide) hs)
  convert h using 1 <;> try rfl
  omega

lemma clear_ptr_ne (n : ℕ) (s : Store) (j : ℕ)
    (h0 : j ≠ 0) (h1 : j ≠ 1) (h15 : j ≠ 15) (h16 : j ≠ 16) :
    (clearEval n s).ptrs j = s.ptrs j := by
  unfold clearEval
  rw [fill_ptr_ne 15 0 n j (prepEval s) h15]
  simp [prepEval,h0,h1,h15,h16]

lemma clear_constants (n : ℕ) (s : Store) :
    (clearEval n s).ptrs 0 = 0 ∧ (clearEval n s).ptrs 1 = 1 := by
  constructor
  · unfold clearEval
    rw [fill_ptr_ne 15 0 n 0 (prepEval s) (by decide)]
    simp [prepEval]
  · unfold clearEval
    rw [fill_ptr_ne 15 0 n 1 (prepEval s) (by decide)]
    simp [prepEval]

lemma clear_frame (n : ℕ) (s : Store) : DataFrame s (clearEval n s) :=
  fill_frame 15 0 n (prepEval s)

lemma clear_memory (n : ℕ) (s : Store) :
    (clearEval n s).imem =
      TupleWriter.writeMemory (s.ptrs 4) (List.replicate n (0:ℤ)) s.imem := by
  unfold clearEval
  rw [fill_memory 15 0 n (prepEval s) (by decide)]
  simp [prepEval]

lemma clear_bitmap (n : ℕ) (s : Store) :
    Bitmap (n := n) (clearEval n s).imem (s.ptrs 4) ∅ := by
  intro v
  rw [clear_memory]
  have hi : v.val < (List.replicate n (0:ℤ)).length := by simpa using v.isLt
  rw [address,TupleWriter.writeMemory_get _ _ _ v.val hi]
  simp

lemma clear_memory_frame (n : ℕ) (s : Store) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (clearEval n s).imem x = s.imem x := by
  rw [clear_memory]
  by_cases hlo : x < s.ptrs 4
  · exact TupleWriter.writeMemory_before _ _ _ _ hlo
  · have hhi : s.ptrs 4 + (n:ℤ) ≤ x := by
      by_contra hbad
      have hnonneg : 0 ≤ x-s.ptrs 4 := by omega
      have hlt : (x-s.ptrs 4).toNat < n := by omega
      let v : Fin n := ⟨(x-s.ptrs 4).toNat,hlt⟩
      have he : x = address (s.ptrs 4) v := by dsimp [address,v]; omega
      exact hx v he
    apply TupleWriter.writeMemory_after
    simpa only [List.length_replicate] using hhi

end StableMSR.Recovery.Compiler.BoundaryProgram

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
theorem table_lookup_program :
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

end StableMSR.Recovery.Compiler.TableLookup




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
theorem table_append_program :
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

end StableMSR.Recovery.Compiler.TableAppend



set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.TableAppendLookup
open TableAppend ComponentMachine TableLookupSemantics

/- A newly appended key matches its original query after copying and storage. -/
lemma appended_match (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (hsep : ∀ i : Fin L, ∀ j : Fin (L+1),
      s.ptrs 3+(i.val:ℤ) ≠ endAddress q L s+(j.val:ℤ)) :
    rowMatches (appendEval q L s).imem ((appendEval q L s).ptrs 2)
      ((appendEval q L s).ptrs 3) L q := by
  intro i
  rw [append_ptr_frame q L s 2 (by simp),append_ptr_frame q L s 3 (by simp)]
  change (appendEval q L s).imem (s.ptrs 3+(i.val:ℤ)) =
    (appendEval q L s).imem (endAddress q L s+(i.val:ℤ))
  rw [append_query q L s hL hsep,append_key q L s hL hsep]

lemma appended_row_payload (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) :
    rowPayload (appendEval q L s).imem ((appendEval q L s).ptrs 2) L q = s.ptrs 17 := by
  rw [append_ptr_frame q L s 2 (by simp)]
  exact append_payload q L s hL

/- The inserted record is the final row, so it overrides every earlier match. -/
lemma appended_lookup (q L : ℕ) (s : Store) (hq : s.ptrs 5 = (q:ℤ))
    (hL : s.ptrs 6 = (L:ℤ))
    (hsep : ∀ i : Fin L, ∀ j : Fin (L+1),
      s.ptrs 3+(i.val:ℤ) ≠ endAddress q L s+(j.val:ℤ)) :
    (TableLookupMachine.blockEval L (q+1) (appendEval q L s)).ptrs 25 = (q:ℤ) ∧
    (TableLookupMachine.blockEval L (q+1) (appendEval q L s)).ptrs 26 = s.ptrs 17 := by
  let t := appendEval q L s
  have hL' : t.ptrs 6 = (L:ℤ) := by
    rw [append_ptr_frame q L s 6 (by simp),hL]
  have hq' : t.ptrs 5 = ((q+1:ℕ):ℤ) := by
    rw [append_count,hq]; push_cast; rfl
  have he := scan_eq_of_last (rowMatches t.imem (t.ptrs 2) (t.ptrs 3) L)
    (rowPayload t.imem (t.ptrs 2) L) (q+1) (q+1) q (by omega)
    (appended_match q L s hL hsep) (by intro j hj _; omega)
  have hs := TableLookup.block_scan L (q+1) (q+1) t hL' hq'
  rw [he] at hs
  exact ⟨hs.1,hs.2.trans (appended_row_payload q L s hL)⟩

def fullCmd : Cmd := .seq appendCmd TableLookupMachine.block
noncomputable def fullEval (q L : ℕ) (s : Store) : Store :=
  TableLookupMachine.blockEval L (q+1) (appendEval q L s)
def cost (q L : ℕ) : ℕ := 4*q+7*L+(q+1)*(11*L+16)+29

lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (q L : ℕ) (s : Store)
    (hq : s.ptrs 5 = (q:ℤ)) (hL : s.ptrs 6 = (L:ℤ)) :
    Executes d fullCmd s (fullEval q L s) (cost q L-1) := by
  have hq' : (appendEval q L s).ptrs 5 = ((q+1:ℕ):ℤ) := by
    rw [append_count,hq]; push_cast; rfl
  have hL' : (appendEval q L s).ptrs 6 = (L:ℤ) := by
    rw [append_ptr_frame q L s 6 (by simp),hL]
  have h := Executes.seq (append_exec d q L s hq hL)
    (TableLookupMachine.block_exec d L (q+1) (appendEval q L s) hL' hq')
  convert h using 1 <;> try rfl
  dsimp [cost]; omega
lemma fullCmd_size : fullCmd.size = 71 := by decide
noncomputable def program : MinSumFPT.Program := compile fullCmd 0
lemma program_length : program.length = 72 := by
  simp [program,compile,compileAt_length,fullCmd_size]
lemma full_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (q L : ℕ) (s : Store) (hq : s.ptrs 5 = (q:ℤ)) (hL : s.ptrs 6 = (L:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[cost q L] (s.state 0 work) =
      (fullEval q L s).haltedState 71 (work+cost q L) 0 := by
  have h := compile_halts (full_exec d q L s hq hL) ω work 0
  have he : cost q L-1+1 = cost q L := by simp [cost]
  simpa only [program,fullCmd_size,he,Nat.add_assoc] using h

lemma full_imem (q L : ℕ) (s : Store) :
    (fullEval q L s).imem = (appendEval q L s).imem :=
  TableLookupMachine.block_imem L (q+1) (appendEval q L s)
lemma full_frame (q L : ℕ) (s : Store) : DataFrame s (fullEval q L s) :=
  (append_frame q L s).trans (TableLookupMachine.block_frame L (q+1) (appendEval q L s))
lemma full_count (q L : ℕ) (s : Store) : (fullEval q L s).ptrs 5 = s.ptrs 5+1 := by
  rw [fullEval,TableLookupMachine.block_ptr_frame L (q+1) (appendEval q L s) 5 (by simp),append_count]
lemma full_ptr_frame (q L : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([0,4,5,18,20,21,22,23,24,25,26,27,28,29,30,32,
      34,35,36,37,38,39,40,41] : List ℕ)) :
    (fullEval q L s).ptrs j = s.ptrs j := by
  rw [fullEval,TableLookupMachine.block_ptr_frame,append_ptr_frame] <;> simp_all

/- The same compiled run constructs a record and retrieves its new payload,
even when earlier records have the same key. -/
theorem table_append_lookup_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 72 ∧
    ∀ (N q L : ℕ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 5 = (q:ℤ) → s.ptrs 6 = (L:ℤ) →
      (∀ i : Fin L, ∀ j : Fin (L+1), s.ptrs 3+(i.val:ℤ) ≠
        s.ptrs 2+(q:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let base := s.ptrs 2+(q:ℤ)*((L:ℤ)+1)
      let steps := 4*q+7*L+(q+1)*(11*L+16)+29
      let result := (MinSumFPT.step P d ω)^[steps] (s.state 0 work)
      result.halted = true ∧ result.work = work+steps ∧
      result.cfg.ptrs 5 = ((q+1:ℕ):ℤ) ∧
      result.cfg.ptrs 25 = (q:ℤ) ∧ result.cfg.ptrs 26 = s.ptrs 17 ∧
      (∀ i : Fin L, result.imem (base+(i.val:ℤ)) = s.imem (s.ptrs 3+(i.val:ℤ))) ∧
      result.imem (base+(L:ℤ)) = s.ptrs 17 ∧
      (∀ i : Fin q, ∀ j : Fin (L+1),
        result.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ x : ℤ, x < base ∨ base+(L:ℤ)+1 ≤ x → result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∉ ([0,4,5,18,20,21,22,23,24,25,26,27,28,29,30,32,
        34,35,36,37,38,39,40,41] : List ℕ) → result.cfg.ptrs j = s.ptrs j) := by
  refine ⟨program,compile_deterministic fullCmd 0,program_length,?_⟩
  intro N q L d s hq hL hsep ω work
  dsimp only
  rw [show 4*q+7*L+(q+1)*(11*L+16)+29 = cost q L by rfl]
  rw [full_machine_execution d q L s hq hL ω work]
  have hf := full_frame q L s
  have hm := full_imem q L s
  have hh := appended_lookup q L s hq hL hsep
  refine ⟨rfl,rfl,?_,hh.1,hh.2,?_,?_,?_,?_,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,
    full_ptr_frame q L s⟩
  · change (fullEval q L s).ptrs 5 = _
    rw [full_count,hq]; push_cast; rfl
  · change ∀ i : Fin L, (fullEval q L s).imem _ = _
    rw [hm]; exact append_key q L s hL hsep
  · change (fullEval q L s).imem _ = _
    rw [hm]; exact append_payload q L s hL
  · change ∀ i : Fin q, ∀ j : Fin (L+1), (fullEval q L s).imem _ = _
    rw [hm]; exact append_old_record q L s hL
  · change ∀ x : ℤ, _ → (fullEval q L s).imem _ = _
    rw [hm]; exact append_memory_frame q L s hL

end StableMSR.Recovery.Compiler.TableAppendLookup


set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.WordBitmap
open ComponentMachine ComponentMemory

/- Mark a digit only when it names a valid positive vertex; zero is padding. -/
def mark (n : ℕ) (base digit : ℤ) (mem : ℤ → ℤ) : ℤ → ℤ :=
  if 0 < digit ∧ digit ≤ (n:ℤ) then Function.update mem (base+digit-1) 1 else mem

def decoded (n : ℕ) (ds : List ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (v.val+1:ℤ) ∈ ds)

lemma mark_frame (n : ℕ) (base digit : ℤ) (mem : ℤ → ℤ) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address base v) : mark n base digit mem x = mem x := by
  unfold mark
  split
  · rename_i h
    let v : Fin n := ⟨(digit-1).toNat,by omega⟩
    have hv : base+digit-1 = address base v := by dsimp [address,v]; omega
    rw [Function.update_of_ne (by rw [hv]; exact hx v)]
  · rfl

lemma mark_bitmap {n : ℕ} (base digit : ℤ) (mem : ℤ → ℤ) (R : Finset (Fin n))
    (hR : Bitmap mem base R) :
    Bitmap (mark n base digit mem) base (R ∪ decoded n [digit]) := by
  intro v
  have hv : 0 ≤ (v.val:ℤ) ∧ (v.val:ℤ) < (n:ℤ) := by constructor; exact_mod_cast Nat.zero_le v.val; exact_mod_cast v.isLt
  by_cases he : digit = (v.val:ℤ)+1
  · have hg : 0 < digit ∧ digit ≤ (n:ℤ) := by omega
    have ha : address base v = base+digit-1 := by dsimp [address]; omega
    simp [mark,hg,ha,decoded,he]
  · have ha : address base v ≠ base+digit-1 := by dsimp [address]; omega
    simp only [mark]
    split
    · rw [Function.update_of_ne ha]
      simpa [decoded,he,Ne.symm he] using hR v
    · simpa [decoded,he,Ne.symm he] using hR v

/- All possible digit branches are padded to six charged steps. -/
def pad5 : Cmd := .seq nop pad4
def markCmd : Cmd := .ite (.pointerLE 10 0) pad5
  (.ite (.pointerLE 10 6)
    (opsCmd [.pointerAdd 11 4 10,.pointerDec 11,.integerStore 11 1]) pad2)
noncomputable def markEval (s : Store) : Store :=
  if s.ptrs 10 ≤ s.ptrs 0 then s else
  if s.ptrs 10 ≤ s.ptrs 6 then
    {s with
      ptrs := Function.update s.ptrs 11 (s.ptrs 4+s.ptrs 10-1)
      imem := Function.update s.imem (s.ptrs 4+s.ptrs 10-1) (s.ptrs 1)}
  else s
lemma mark_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d markCmd s (markEval s) 6 := by
  by_cases h : s.ptrs 10 ≤ s.ptrs 0
  · have hp : Executes d pad5 s s 5 := Executes.seq (nop_exec d s) (pad4_exec d s)
    simpa [markCmd,markEval,h] using Executes.ite_true (c:=Cond.pointerLE 10 0) (no:=Cmd.ite (.pointerLE 10 6) (opsCmd [.pointerAdd 11 4 10,.pointerDec 11,.integerStore 11 1]) pad2) h hp
  · by_cases hn : s.ptrs 10 ≤ s.ptrs 6
    · have hp := ops_exec d [.pointerAdd 11 4 10,.pointerDec 11,.integerStore 11 1] s
      have hh := Executes.ite_false (c:=Cond.pointerLE 10 0) (yes:=pad5) h
        (Executes.ite_true (c:=Cond.pointerLE 10 6) (no:=pad2) hn hp)
      simpa [markCmd,markEval,h,hn,evalOps,Op.eval,Function.update_idem] using hh
    · simpa [markCmd,markEval,h,hn] using
        Executes.ite_false (c:=Cond.pointerLE 10 0) (yes:=pad5) h
          (Executes.ite_false (c:=Cond.pointerLE 10 6)
            (yes:=opsCmd [.pointerAdd 11 4 10,.pointerDec 11,.integerStore 11 1]) hn (pad2_exec d s))
lemma mark_ptr_frame (s : Store) (j : ℕ) (hj : j ≠ 11) :
    (markEval s).ptrs j = s.ptrs j := by
  simp only [markEval]; split <;> (try split) <;> simp [hj]
lemma mark_data_frame (s : Store) : DataFrame s (markEval s) := by
  simp only [markEval]; split <;> (try split) <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

def stepCmd : Cmd := .seq (.atom (.integerLoad 10 7))
  (.seq markCmd (opsCmd [.pointerInc 7,.pointerInc 8]))
noncomputable def step (s : Store) : Store :=
  incPtr (incPtr (markEval (setPtr s 10 (s.imem (s.ptrs 7)))) 7) 8
lemma step_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d stepCmd s (step s) 9 := by
  have h := Executes.seq (Executes.atom (.integerLoad 10 7) s)
    (Executes.seq (mark_exec d _) (ops_exec d [.pointerInc 7,.pointerInc 8] _))
  simpa [stepCmd,step,incPtr,setPtr,evalOps,Op.eval] using h
lemma step_ptr_frame (s : Store) (j : ℕ) (hj : j ∉ ([7,8,10,11] : List ℕ)) :
    (step s).ptrs j = s.ptrs j := by
  have h7 : j ≠ 7 := by simp_all
  have h8 : j ≠ 8 := by simp_all
  have h10 : j ≠ 10 := by simp_all
  have h11 : j ≠ 11 := by simp_all
  simp [step,incPtr,setPtr,mark_ptr_frame,h7,h8,h10,h11]
lemma step_cursor (s : Store) : (step s).ptrs 7 = s.ptrs 7+1 := by
  simp [step,incPtr,setPtr,mark_ptr_frame]
lemma step_index (s : Store) : (step s).ptrs 8 = s.ptrs 8+1 := by
  simp [step,incPtr,setPtr,mark_ptr_frame]
lemma step_frame (s : Store) : DataFrame s (step s) := by
  exact (mark_data_frame (setPtr s 10 (s.imem (s.ptrs 7)))).trans
    (show DataFrame (markEval _) (step s) from ⟨rfl,rfl,rfl,rfl,rfl⟩)
lemma step_memory (n : ℕ) (s : Store) (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hn : s.ptrs 6 = (n:ℤ)) :
    (step s).imem = mark n (s.ptrs 4) (s.imem (s.ptrs 7)) s.imem := by
  simp [step,incPtr,setPtr,markEval,mark,h0,h1,hn]
  split <;> (try split) <;> simp_all <;> omega

def scanCmd : Cmd := .seq (opsCmd [.pointerCopy 7 3,.pointerConst 8 1])
  (.whileDo (.pointerLE 8 43) stepCmd)
noncomputable def scanEval (w : ℕ) (s : Store) : Store :=
  step^[w] (setPtr (setPtr s 7 (s.ptrs 3)) 8 1)
lemma scan_exec {N : ℕ} (d : Point N → Point N → ℝ) (w : ℕ) (s : Store)
    (hw : s.ptrs 43 = (w:ℤ)) :
    Executes d scanCmd s (scanEval w s) (11*w+4) := by
  have hs : Executes d (opsCmd [.pointerCopy 7 3,.pointerConst 8 1]) s
      (setPtr (setPtr s 7 (s.ptrs 3)) 8 1) 2 := by
    simpa [evalOps,Op.eval,setPtr] using ops_exec d [.pointerCopy 7 3,.pointerConst 8 1] s
  have hl := fixed_loop_exec d stepCmd step 8 43 9 (w:ℤ)
    (fun t _ => step_exec d t) step_index (fun t => step_ptr_frame t 43 (by simp)) w
    (setPtr (setPtr s 7 (s.ptrs 3)) 8 1) (by simpa [setPtr] using hw) (by simp [setPtr])
  convert Executes.seq hs hl using 1 <;> try rfl
  omega

/- A scan reads the ordinary source array, whose cells avoid the bitmap. -/
lemma steps_bitmap (n : ℕ) (ds : List ℤ) (s : Store) (R : Finset (Fin n))
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1) (hn : s.ptrs 6 = (n:ℤ))
    (hR : Bitmap s.imem (s.ptrs 4) R)
    (hin : ∀ i : Fin ds.length, s.imem (s.ptrs 7+(i.val:ℤ)) = ds[i.val])
    (hsep : ∀ i : Fin ds.length, ∀ v : Fin n,
      s.ptrs 7+(i.val:ℤ) ≠ address (s.ptrs 4) v) :
    Bitmap (step^[ds.length] s).imem (s.ptrs 4) (R ∪ decoded n ds) := by
  induction ds generalizing s R with
  | nil => simpa [decoded] using hR
  | cons a ds ih =>
    have ha : s.imem (s.ptrs 7) = a := by simpa using hin ⟨0,by simp⟩
    have hm := step_memory n s h0 h1 hn
    rw [ha] at hm
    have hnext (i : Fin ds.length) : (step s).imem ((step s).ptrs 7+(i.val:ℤ)) = ds[i.val] := by
      rw [step_cursor,hm,mark_frame]
      · simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hin ⟨i.val+1,by simpa using i.isLt⟩
      · intro v
        simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hsep ⟨i.val+1,by simpa using i.isLt⟩ v
    have hs : ∀ i : Fin ds.length, ∀ v : Fin n,
        (step s).ptrs 7+(i.val:ℤ) ≠ address ((step s).ptrs 4) v := by
      intro i v
      rw [step_cursor,step_ptr_frame s 4 (by simp)]
      simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hsep ⟨i.val+1,by simpa using i.isLt⟩ v
    have hB : Bitmap (step s).imem ((step s).ptrs 4) (R ∪ decoded n [a]) := by
      rw [step_ptr_frame s 4 (by simp),hm]
      exact mark_bitmap _ _ _ R hR
    have h := ih (step s) (R ∪ decoded n [a])
      (by rw [step_ptr_frame s 0 (by simp),h0])
      (by rw [step_ptr_frame s 1 (by simp),h1])
      (by rw [step_ptr_frame s 6 (by simp),hn]) hB hnext hs
    rw [step_ptr_frame s 4 (by simp)] at h
    rw [List.length_cons,Function.iterate_succ_apply]
    convert h using 1
    ext v; simp [decoded,or_assoc]

lemma steps_memory_frame (n w : ℕ) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1) (hn : s.ptrs 6 = (n:ℤ))
    (x : ℤ) (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (step^[w] s).imem x = s.imem x := by
  induction w generalizing s with
  | zero => rfl
  | succ w ih =>
    rw [Function.iterate_succ_apply]
    rw [ih (step s) (by rw [step_ptr_frame s 0 (by simp),h0])
      (by rw [step_ptr_frame s 1 (by simp),h1])
      (by rw [step_ptr_frame s 6 (by simp),hn])
      (by rwa [step_ptr_frame s 4 (by simp)])]
    rw [step_memory n s h0 h1 hn,mark_frame n (s.ptrs 4) _ _ x hx]

/- Clear the result before scanning; no supplied bitmap is an input invariant. -/
def fullCmd : Cmd := .seq BoundaryProgram.clearCmd scanCmd
noncomputable def fullEval (n w : ℕ) (s : Store) : Store := scanEval w (BoundaryProgram.clearEval n s)
lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n w : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) :
    Executes d fullCmd s (fullEval n w s) (4*n+11*w+11) := by
  have h := Executes.seq (BoundaryProgram.clear_exec d n s hn)
    (scan_exec d w (BoundaryProgram.clearEval n s) (by
      rw [BoundaryProgram.clear_ptr_ne n s 43 (by decide) (by decide) (by decide) (by decide),hw]))
  convert h using 1 <;> try rfl
  omega
lemma full_ptr_frame (n w : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([0,1,7,8,10,11,15,16] : List ℕ)) : (fullEval n w s).ptrs j = s.ptrs j := by
  have hstep : j ∉ ([7,8,10,11] : List ℕ) := by simp_all
  unfold fullEval scanEval
  rw [iterate_preserves _ (fun t => t.ptrs j) (fun t => step_ptr_frame t j hstep)]
  simp only [setPtr]
  have h7 : j ≠ 7 := by simp_all
  have h8 : j ≠ 8 := by simp_all
  rw [Function.update_of_ne h8,Function.update_of_ne h7,BoundaryProgram.clear_ptr_ne] <;> simp_all
lemma full_bitmap (n : ℕ) (ds : List ℤ) (s : Store) (hn : s.ptrs 6 = (n:ℤ))
    (hin : ∀ i : Fin ds.length, s.imem (s.ptrs 3+(i.val:ℤ)) = ds[i.val])
    (hsep : ∀ i : Fin ds.length, ∀ v : Fin n,
      s.ptrs 3+(i.val:ℤ) ≠ address (s.ptrs 4) v) :
    Bitmap (fullEval n ds.length s).imem (s.ptrs 4) (decoded n ds) := by
  let t := setPtr (setPtr (BoundaryProgram.clearEval n s) 7 (s.ptrs 3)) 8 1
  have hptr (j : ℕ) (hj : j ∉ ([0,1,7,8,15,16] : List ℕ)) : t.ptrs j = s.ptrs j := by
    dsimp [t,setPtr]
    have h7 : j ≠ 7 := by simp_all
    have h8 : j ≠ 8 := by simp_all
    rw [Function.update_of_ne h8,Function.update_of_ne h7,BoundaryProgram.clear_ptr_ne] <;> simp_all
  have ht7 : t.ptrs 7 = s.ptrs 3 := by simp [t,setPtr]
  have hb : Bitmap (n := n) t.imem (t.ptrs 4) ∅ := by
    rw [hptr 4 (by simp)]
    exact BoundaryProgram.clear_bitmap n s
  have h := steps_bitmap n ds t ∅
    (by simpa [t,setPtr] using (BoundaryProgram.clear_constants n s).1)
    (by simpa [t,setPtr] using (BoundaryProgram.clear_constants n s).2)
    (by rw [hptr 6 (by simp),hn]) hb (by
      intro i
      rw [ht7]
      change (BoundaryProgram.clearEval n s).imem _ = _
      rw [BoundaryProgram.clear_memory_frame n s _ (hsep i)]
      exact hin i) (by
      intro i v
      rw [ht7,hptr 4 (by simp)]
      exact hsep i v)
  rw [hptr 4 (by simp)] at h
  simpa [fullEval,scanEval,t,BoundaryProgram.clear_ptr_ne] using h
lemma full_memory_frame (n w : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ))
    (x : ℤ) (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (fullEval n w s).imem x = s.imem x := by
  unfold fullEval scanEval
  rw [steps_memory_frame n w _ (by simpa [setPtr] using (BoundaryProgram.clear_constants n s).1)
    (by simpa [setPtr] using (BoundaryProgram.clear_constants n s).2)
    (by simpa [setPtr,BoundaryProgram.clear_ptr_ne] using hn)]
  · exact BoundaryProgram.clear_memory_frame n s x hx
  · simpa [setPtr,BoundaryProgram.clear_ptr_ne] using hx
lemma full_frame (n w : ℕ) (s : Store) : DataFrame s (fullEval n w s) :=
  (BoundaryProgram.clear_frame n s).trans
    (iterate_frame step step_frame w (setPtr (setPtr (BoundaryProgram.clearEval n s) 7 _) 8 1))
lemma fullCmd_size : fullCmd.size = 32 := by decide

end StableMSR.Recovery.Compiler.WordBitmap
set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.WordBitmap
noncomputable def program : MinSumFPT.Program := compile fullCmd 0
lemma machine_execution {N : ℕ} (d : Point N → Point N → ℝ) (n w : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[4*n+11*w+12] (s.state 0 work) =
      (fullEval n w s).haltedState 32 (work+(4*n+11*w+12)) 0 := by
  simpa [program,fullCmd_size,Nat.add_assoc] using compile_halts (full_exec d n w s hn hw) ω work 0

/- A uniform decoder computes characteristic keys from ordinary integer words. -/
theorem word_bitmap_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 33 ∧
    ∀ (N n : ℕ) (ds : List ℤ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (ds.length:ℤ) →
      (∀ i : Fin ds.length, s.imem (s.ptrs 3+(i.val:ℤ)) = ds[i.val]) →
      (∀ i : Fin ds.length, ∀ v : Fin n, s.ptrs 3+(i.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let result := (MinSumFPT.step P d ω)^[4*n+11*ds.length+12] (s.state 0 work)
      result.halted = true ∧ result.work = work+(4*n+11*ds.length+12) ∧
      (∀ v : Fin n, result.imem (s.ptrs 4+(v.val:ℤ)) =
        if (v.val+1:ℤ) ∈ ds then 1 else 0) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ)) → result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∉ ([0,1,7,8,10,11,15,16] : List ℕ) → result.cfg.ptrs j = s.ptrs j) := by
  refine ⟨program,compile_deterministic fullCmd 0,?_,?_⟩
  · simp [program,compile,fullCmd_size]
  intro N n ds d s hn hw hin hsep ω work
  dsimp only
  rw [machine_execution d n ds.length s hn hw ω work]
  have hf := full_frame n ds.length s
  refine ⟨rfl,rfl,?_,full_memory_frame n ds.length s hn,hf.1,hf.2.1,
    hf.2.2.1,hf.2.2.2.1,full_ptr_frame n ds.length s⟩
  intro v
  change (fullEval n ds.length s).imem _ = _
  have h := full_bitmap n ds s hn hin hsep v
  simpa [decoded,ComponentMemory.address,Store.haltedState,Store.state] using h
end StableMSR.Recovery.Compiler.WordBitmap
set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.WordRecord
open ComponentMachine ComponentMemory

def redirectCmd : Cmd := opsCmd [.pointerCopy 42 3,.pointerCopy 3 4]
def redirect (s : Store) : Store := setPtr (setPtr s 42 (s.ptrs 3)) 3 (s.ptrs 4)
def restore (s : Store) : Store := setPtr s 3 (s.ptrs 42)
def fullCmd : Cmd := .seq WordBitmap.fullCmd (.seq redirectCmd
  (.seq TableAppendLookup.fullCmd (.atom (.pointerCopy 3 42))))
noncomputable def fullEval (n w q : ℕ) (s : Store) : Store :=
  restore (TableAppendLookup.fullEval q n (redirect (WordBitmap.fullEval n w s)))
def cost (n w q : ℕ) : ℕ := 4*q+11*n+11*w+(q+1)*(11*n+16)+43
lemma redirect_ptr (s : Store) (j : ℕ) (h3 : j ≠ 3) (h42 : j ≠ 42) :
    (redirect s).ptrs j = s.ptrs j := by simp [redirect,setPtr,h3,h42]
lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n w q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) (hq : s.ptrs 5 = (q:ℤ)) :
    Executes d fullCmd s (fullEval n w q s) (cost n w q-1) := by
  have hr (t : Store) : Executes d redirectCmd t (redirect t) 2 := by
    simpa [redirectCmd,redirect,evalOps,Op.eval,setPtr] using
      ops_exec d [.pointerCopy 42 3,.pointerCopy 3 4] t
  have hn' : (redirect (WordBitmap.fullEval n w s)).ptrs 6 = (n:ℤ) := by
    rw [redirect_ptr _ 6 (by decide) (by decide),WordBitmap.full_ptr_frame _ _ _ 6 (by simp),hn]
  have hq' : (redirect (WordBitmap.fullEval n w s)).ptrs 5 = (q:ℤ) := by
    rw [redirect_ptr _ 5 (by decide) (by decide),WordBitmap.full_ptr_frame _ _ _ 5 (by simp),hq]
  have h := Executes.seq (WordBitmap.full_exec d n w s hn hw)
    (Executes.seq (hr _)
      (Executes.seq (TableAppendLookup.full_exec d q n _ hq' hn')
        (Executes.atom (.pointerCopy 3 42) _)))
  convert h using 1 <;> try rfl
  simp only [cost,TableAppendLookup.cost]
  omega
lemma fullCmd_size : fullCmd.size = 106 := by decide
noncomputable def program : MinSumFPT.Program := compile fullCmd 0
lemma machine_execution {N : ℕ} (d : Point N → Point N → ℝ) (n w q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) (hq : s.ptrs 5 = (q:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[cost n w q] (s.state 0 work) =
      (fullEval n w q s).haltedState 106 (work+cost n w q) 0 := by
  have h := compile_halts (full_exec d n w q s hn hw hq) ω work 0
  have he : cost n w q-1+1 = cost n w q := by simp [cost]
  simpa only [program,fullCmd_size,he,Nat.add_assoc] using h

/- The inserted table key comes from the bitmap actually computed by decoding. -/
lemma record_values (n : ℕ) (ds : List ℤ) (q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hq : s.ptrs 5 = (q:ℤ))
    (hin : ∀ i : Fin ds.length, s.imem (s.ptrs 3+(i.val:ℤ)) = ds[i.val])
    (hwords : ∀ i : Fin ds.length, ∀ v : Fin n, s.ptrs 3+(i.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ))
    (hrecord : ∀ v : Fin n, ∀ j : Fin (n+1), s.ptrs 4+(v.val:ℤ) ≠
      s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) :
    (fullEval n ds.length q s).ptrs 25 = (q:ℤ) ∧
    (fullEval n ds.length q s).ptrs 26 = s.ptrs 17 ∧
    (∀ v : Fin n, (fullEval n ds.length q s).imem
      (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(v.val:ℤ)) = if (v.val+1:ℤ) ∈ ds then 1 else 0) ∧
    (fullEval n ds.length q s).imem (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(n:ℤ)) = s.ptrs 17 := by
  let u := WordBitmap.fullEval n ds.length s
  let t := redirect u
  have hp (j : ℕ) (hj : j ∉ ([0,1,3,7,8,10,11,15,16,42] : List ℕ)) : t.ptrs j = s.ptrs j := by
    rw [redirect_ptr]
    · exact WordBitmap.full_ptr_frame _ _ _ j (by simp_all)
    · simp_all
    · simp_all
  have h3 : t.ptrs 3 = s.ptrs 4 := by
    change (redirect u).ptrs 3 = _
    simp only [redirect,setPtr,Function.update_self]
    exact WordBitmap.full_ptr_frame n ds.length s 4 (by simp)
  have hw' : t.ptrs 6 = (n:ℤ) := by rw [hp 6 (by simp),hn]
  have hq' : t.ptrs 5 = (q:ℤ) := by rw [hp 5 (by simp),hq]
  have hs : ∀ v : Fin n, ∀ j : Fin (n+1), t.ptrs 3+(v.val:ℤ) ≠
      TableAppend.endAddress q n t+(j.val:ℤ) := by
    intro v j
    rw [h3]
    simpa only [TableAppend.endAddress,hp 2 (by simp)] using hrecord v j
  have hh := TableAppendLookup.appended_lookup q n t hq' hw' hs
  have hm := TableAppendLookup.full_imem q n t
  have hb := WordBitmap.full_bitmap n ds s hn hin hwords
  have hk (v : Fin n) : (TableAppendLookup.fullEval q n t).imem
      (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(v.val:ℤ)) = if (v.val+1:ℤ) ∈ ds then 1 else 0 := by
    rw [hm]
    have h := TableAppend.append_key q n t hw' hs v
    rw [TableAppend.endAddress,hp 2 (by simp),h3] at h
    rw [h]
    simpa [t,u,redirect,setPtr,WordBitmap.decoded,address] using hb v
  have hv : (TableAppendLookup.fullEval q n t).imem
      (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(n:ℤ)) = s.ptrs 17 := by
    rw [hm]
    have h := TableAppend.append_payload q n t hw'
    simpa only [TableAppend.endAddress,hp 2 (by simp),hp 17 (by simp)] using h
  exact ⟨hh.1,hh.2.trans (hp 17 (by simp)),hk,hv⟩

lemma full_frame (n w q : ℕ) (s : Store) : DataFrame s (fullEval n w q s) :=
  (WordBitmap.full_frame n w s).trans
    (TableAppendLookup.full_frame q n (redirect (WordBitmap.fullEval n w s)))
lemma word_pointer (n w q : ℕ) (s : Store) : (fullEval n w q s).ptrs 3 = s.ptrs 3 := by
  unfold fullEval restore
  simp only [setPtr,Function.update_self]
  rw [TableAppendLookup.full_ptr_frame q n _ 42 (by simp)]
  simp [redirect,setPtr,WordBitmap.full_ptr_frame]
lemma count_updated (n w q : ℕ) (s : Store) : (fullEval n w q s).ptrs 5 = s.ptrs 5+1 := by
  unfold fullEval restore
  simp only [setPtr,Function.update_of_ne (show (5:ℕ) ≠ 3 by decide)]
  rw [TableAppendLookup.full_count,redirect_ptr _ 5 (by decide) (by decide),
    WordBitmap.full_ptr_frame _ _ _ 5 (by simp)]

lemma full_memory_frame (n w q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ))
    (x : ℤ) (hbitmap : ∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ))
    (hrecord : x < s.ptrs 2+(q:ℤ)*((n:ℤ)+1) ∨
      s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(n:ℤ)+1 ≤ x) :
    (fullEval n w q s).imem x = s.imem x := by
  let t := redirect (WordBitmap.fullEval n w s)
  have hn' : t.ptrs 6 = (n:ℤ) := by
    rw [redirect_ptr _ 6 (by decide) (by decide),WordBitmap.full_ptr_frame _ _ _ 6 (by simp),hn]
  have h2 : t.ptrs 2 = s.ptrs 2 := by
    rw [redirect_ptr _ 2 (by decide) (by decide),WordBitmap.full_ptr_frame _ _ _ 2 (by simp)]
  change (TableAppendLookup.fullEval q n t).imem x = _
  rw [TableAppendLookup.full_imem,TableAppend.append_memory_frame q n t hn' x]
  · exact WordBitmap.full_memory_frame n w s hn x hbitmap
  · simpa only [TableAppend.endAddress,h2] using hrecord

lemma old_records (n w q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ))
    (hspace : ∀ i : Fin q, ∀ j : Fin (n+1), ∀ v : Fin n,
      s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ))
    (i : Fin q) (j : Fin (n+1)) :
    (fullEval n w q s).imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) =
      s.imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) := by
  apply full_memory_frame n w q s hn _ (hspace i j)
  left
  have hi : (i.val:ℤ)+1 ≤ (q:ℤ) := by have := i.isLt; omega
  have hj : (j.val:ℤ) < (n:ℤ)+1 := by have := j.isLt; omega
  have hp : 0 < (n:ℤ)+1 := by omega
  nlinarith

/- One actual run decodes an integer word, constructs its subset-key record,
and retrieves the stored payload using last-match lookup. -/
end StableMSR.Recovery.Compiler.WordRecord
set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.CatalogSweep
open ComponentMachine ComponentMemory

lemma record_ptr_frame (n w q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([0,1,3,4,5,7,8,10,11,15,16,18,20,21,22,23,24,25,26,27,28,29,30,32,
      34,35,36,37,38,39,40,41,42] : List ℕ)) :
    (WordRecord.fullEval n w q s).ptrs j = s.ptrs j := by
  have h3 : j ≠ 3 := by simp_all
  have h42 : j ≠ 42 := by simp_all
  unfold WordRecord.fullEval WordRecord.restore
  simp only [setPtr,Function.update_of_ne h3]
  rw [TableAppendLookup.full_ptr_frame,WordRecord.redirect_ptr _ j h3 h42,
    WordBitmap.full_ptr_frame] <;> simp_all

def tailCmd : Cmd := opsCmd [.pointerCopy 4 44,.pointerAdd 3 3 47,.pointerInc 46]
def advance (s : Store) : Store :=
  setPtr (setPtr (setPtr s 4 (s.ptrs 44)) 3 (s.ptrs 3+s.ptrs 47)) 46 (s.ptrs 46+1)
def body : Cmd := .seq WordRecord.fullCmd tailCmd
noncomputable def row (n w q : ℕ) (s : Store) : Store := advance (WordRecord.fullEval n w q s)
noncomputable def run (n w : ℕ) : ℕ → ℕ → Store → Store
  | _,0,s => s
  | q,m+1,s => run n w (q+1) m (row n w q s)

def loopCost (n w : ℕ) : ℕ → ℕ → ℕ
  | _,0 => 2
  | q,m+1 => WordRecord.cost n w q+4+loopCost n w (q+1) m

lemma row_exec {N : ℕ} (d : Point N → Point N → ℝ) (n w q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) (hq : s.ptrs 5 = (q:ℤ)) :
    Executes d body s (row n w q s) (WordRecord.cost n w q+2) := by
  have ht := ops_exec d [.pointerCopy 4 44,.pointerAdd 3 3 47,.pointerInc 46]
    (WordRecord.fullEval n w q s)
  have h := Executes.seq (WordRecord.full_exec d n w q s hn hw hq) ht
  convert h using 1 <;> try rfl

lemma row_ptr_frame (n w q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([0,1,3,4,5,7,8,10,11,15,16,18,20,21,22,23,24,25,26,27,28,29,30,32,
      34,35,36,37,38,39,40,41,42,46] : List ℕ)) : (row n w q s).ptrs j = s.ptrs j := by
  have h3 : j ≠ 3 := by simp_all
  have h4 : j ≠ 4 := by simp_all
  have h46 : j ≠ 46 := by simp_all
  simp only [row,advance,setPtr,Function.update_of_ne h3,Function.update_of_ne h4,
    Function.update_of_ne h46]
  apply record_ptr_frame
  simp_all
lemma row_count (n w q : ℕ) (s : Store) : (row n w q s).ptrs 5 = s.ptrs 5+1 := by
  simp only [row,advance,setPtr,Function.update_of_ne (show (5:ℕ) ≠ 46 by decide),
    Function.update_of_ne (show (5:ℕ) ≠ 3 by decide),Function.update_of_ne (show (5:ℕ) ≠ 4 by decide)]
  exact WordRecord.count_updated n w q s
lemma row_index (n w q : ℕ) (s : Store) : (row n w q s).ptrs 46 = s.ptrs 46+1 := by
  simp [row,advance,setPtr,record_ptr_frame]
lemma row_cursor (n w q : ℕ) (s : Store) :
    (row n w q s).ptrs 3 = s.ptrs 3+s.ptrs 47 := by
  simp [row,advance,setPtr,WordRecord.word_pointer,record_ptr_frame]
lemma row_workspace (n w q : ℕ) (s : Store) (h : s.ptrs 44 = s.ptrs 4) :
    (row n w q s).ptrs 4 = s.ptrs 4 := by
  simp [row,advance,setPtr,record_ptr_frame,h]
lemma row_imem (n w q : ℕ) (s : Store) :
    (row n w q s).imem = (WordRecord.fullEval n w q s).imem := rfl
lemma row_frame (n w q : ℕ) (s : Store) : DataFrame s (row n w q s) :=
  WordRecord.full_frame n w q s

lemma run_ptr_frame (n w q m : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([0,1,3,4,5,7,8,10,11,15,16,18,20,21,22,23,24,25,26,27,28,29,30,32,
      34,35,36,37,38,39,40,41,42,46] : List ℕ)) :
    (run n w q m s).ptrs j = s.ptrs j := by
  induction m generalizing q s with
  | zero => rfl
  | succ m ih => rw [run,ih,row_ptr_frame n w q s j hj]
lemma run_count (n w q m : ℕ) (s : Store) :
    (run n w q m s).ptrs 5 = s.ptrs 5+(m:ℤ) := by
  induction m generalizing q s with
  | zero => simp [run]
  | succ m ih => rw [run,ih,row_count]; push_cast; ring
lemma run_cursor (n w q m : ℕ) (s : Store) :
    (run n w q m s).ptrs 3 = s.ptrs 3+(m:ℤ)*s.ptrs 47 := by
  induction m generalizing q s with
  | zero => simp [run]
  | succ m ih =>
    rw [run,ih,row_cursor,row_ptr_frame n w q s 47 (by simp)]
    push_cast; ring
lemma run_frame (n w q m : ℕ) (s : Store) : DataFrame s (run n w q m s) := by
  induction m generalizing q s with
  | zero => exact DataFrame.refl _
  | succ m ih => exact (row_frame n w q s).trans (ih (q+1) (row n w q s))

lemma loop_exec {N : ℕ} (d : Point N → Point N → ℝ) (n w q m : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) (hq : s.ptrs 5 = (q:ℤ))
    (hstop : s.ptrs 46+(m:ℤ)-1 = s.ptrs 45) :
    Executes d (.whileDo (.pointerLE 46 45) body) s (run n w q m s) (loopCost n w q m) := by
  induction m generalizing q s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test]; omega
  | succ m ih =>
    have hg : (Cond.pointerLE 46 45).test s := by simp only [Cond.test]; omega
    have hq' : (row n w q s).ptrs 5 = ((q+1:ℕ):ℤ) := by rw [row_count,hq]; push_cast; rfl
    have hr := ih (q+1) (row n w q s)
      (by rw [row_ptr_frame n w q s 6 (by simp),hn])
      (by rw [row_ptr_frame n w q s 43 (by simp),hw]) hq'
      (by rw [row_index,row_ptr_frame n w q s 45 (by simp)]; push_cast at hstop; omega)
    have h := Executes.while_true hg (row_exec d n w q s hn hw hq) hr
    convert h using 1 <;> try rfl
    simp only [loopCost]; omega

def setupOps : List Op :=
  [.pointerCopy 44 4,.pointerCopy 45 48,.pointerDec 45,.pointerConst 46 0,
   .pointerCopy 47 43,.pointerInc 47]
def setup (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 44 (s.ptrs 4)) 45 (s.ptrs 48-1)) 46 0) 47 (s.ptrs 43+1)
def fullCmd : Cmd := .seq (opsCmd setupOps) (.whileDo (.pointerLE 46 45) body)
noncomputable def fullEval (n w q m : ℕ) (s : Store) : Store := run n w q m (setup s)
lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n w q m : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) (hq : s.ptrs 5 = (q:ℤ))
    (hm : s.ptrs 48 = (m:ℤ)) :
    Executes d fullCmd s (fullEval n w q m s) (6+loopCost n w q m) := by
  have hs : Executes d (opsCmd setupOps) s (setup s) 6 := by
    simpa [setupOps,setup,evalOps,Op.eval,setPtr,Function.update_idem] using ops_exec d setupOps s
  have hl := loop_exec d n w q m (setup s) (by simpa [setup,setPtr] using hn)
    (by simpa [setup,setPtr] using hw) (by simpa [setup,setPtr] using hq)
    (by simp [setup,setPtr,hm])
  exact Executes.seq hs hl
lemma fullCmd_size : fullCmd.size = 118 := by decide
noncomputable def program : MinSumFPT.Program := compile fullCmd 0
lemma machine_execution {N : ℕ} (d : Point N → Point N → ℝ) (n w q m : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) (hq : s.ptrs 5 = (q:ℤ))
    (hm : s.ptrs 48 = (m:ℤ)) (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[7+loopCost n w q m] (s.state 0 work) =
      (fullEval n w q m s).haltedState 118 (work+(7+loopCost n w q m)) 0 := by
  simpa only [program,fullCmd_size,show 6+loopCost n w q m+1 = 7+loopCost n w q m by omega,
    show work+(6+loopCost n w q m)+1 = work+(7+loopCost n w q m) by omega] using
    compile_halts (full_exec d n w q m s hn hw hq hm) ω work 0

lemma cost_mono (n w q r : ℕ) (h : q ≤ r) : WordRecord.cost n w q ≤ WordRecord.cost n w r := by
  dsimp [WordRecord.cost]
  have := Nat.mul_le_mul_right (11*n+16) (show q+1 ≤ r+1 by omega)
  omega
lemma loop_cost_bound (n w q m : ℕ) :
    loopCost n w q m ≤ m*(WordRecord.cost n w (q+m)+4)+2 := by
  induction m generalizing q with
  | zero => simp [loopCost]
  | succ m ih =>
    have hr := ih (q+1)
    have he : q+1+m = q+(m+1) := by omega
    rw [he] at hr
    have hc := cost_mono n w q (q+(m+1)) (by omega)
    simp only [loopCost]
    nlinarith
end StableMSR.Recovery.Compiler.CatalogSweep
set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.CatalogSweep

/- Ordinary array layout and immutable catalog data; no output records assumed. -/
structure Ready (n w q : ℕ) (ws : List (Fin w → ℤ)) (s : Store) : Prop where
  vertices : s.ptrs 6 = (n:ℤ)
  width : s.ptrs 43 = (w:ℤ)
  count : s.ptrs 5 = (q:ℤ)
  stride : s.ptrs 47 = (w:ℤ)+1
  workspace : s.ptrs 44 = s.ptrs 4
  encoded : ∀ a : Fin ws.length, ∀ i : Fin w,
    s.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ)) = ws[a.val] i
  source_bitmap : ∀ a : Fin ws.length, ∀ i : Fin w, ∀ v : Fin n,
    s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ)
  source_table : ∀ a : Fin ws.length, ∀ i : Fin w,
    ∀ r : Fin (q+ws.length), ∀ j : Fin (n+1),
    s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) ≠
      s.ptrs 2+(r.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)
  bitmap_table : ∀ v : Fin n, ∀ r : Fin (q+ws.length), ∀ j : Fin (n+1),
    s.ptrs 4+(v.val:ℤ) ≠ s.ptrs 2+(r.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)

lemma row_memory_frame (n w q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ)) (x : ℤ)
    (hb : ∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ))
    (hr : ∀ j : Fin (n+1), x ≠ s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) :
    (row n w q s).imem x = s.imem x := by
  rw [row_imem]
  apply WordRecord.full_memory_frame n w q s hn x hb
  have h := TableAppend.outside_interval (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)) x (n+1) hr
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using h

lemma ready_tail {n w q : ℕ} {f : Fin w → ℤ} {ws : List (Fin w → ℤ)} {s : Store}
    (h : Ready n w q (f::ws) s) : Ready n w (q+1) ws (row n w q s) := by
  have hp (j : ℕ) (hj : j ∈ ([2,6,17,43,44,47] : List ℕ)) :
      (row n w q s).ptrs j = s.ptrs j := by
    apply row_ptr_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  have h4 := row_workspace n w q s h.workspace
  have h3 : (row n w q s).ptrs 3 = s.ptrs 3+((w:ℤ)+1) := by rw [row_cursor,h.stride]
  have hlen : (q+1)+ws.length = q+(f::ws).length := by simp; omega
  constructor
  · rw [hp 6 (by simp),h.vertices]
  · rw [hp 43 (by simp),h.width]
  · rw [row_count,h.count]; push_cast; rfl
  · rw [hp 47 (by simp),h.stride]
  · rw [hp 44 (by simp),h4]; exact h.workspace
  · intro a i
    rw [h3]
    have he : s.ptrs 3+((w:ℤ)+1)+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) =
        s.ptrs 3+((a.val+1:ℕ):ℤ)*((w:ℤ)+1)+(i.val:ℤ) := by push_cast; ring
    rw [he,row_memory_frame n w q s h.vertices]
    · simpa using h.encoded ⟨a.val+1,by simp⟩ i
    · exact h.source_bitmap ⟨a.val+1,by simp⟩ i
    · exact h.source_table ⟨a.val+1,by simp⟩ i ⟨q,by simp⟩
  · intro a i v
    rw [h3,h4]
    have he : s.ptrs 3+((w:ℤ)+1)+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) =
        s.ptrs 3+((a.val+1:ℕ):ℤ)*((w:ℤ)+1)+(i.val:ℤ) := by push_cast; ring
    rw [he]
    exact h.source_bitmap ⟨a.val+1,by simp⟩ i v
  · intro a i r j
    rw [h3,hp 2 (by simp)]
    have he : s.ptrs 3+((w:ℤ)+1)+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) =
        s.ptrs 3+((a.val+1:ℕ):ℤ)*((w:ℤ)+1)+(i.val:ℤ) := by push_cast; ring
    rw [he]
    exact h.source_table ⟨a.val+1,by simp⟩ i ⟨r.val,by rw [←hlen]; exact r.isLt⟩ j
  · intro v r j
    rw [h4,hp 2 (by simp)]
    exact h.bitmap_table v ⟨r.val,by rw [←hlen]; exact r.isLt⟩ j

/- The entire loop frames all cells outside its workspace and new records. -/
lemma run_memory_frame (n w q : ℕ) (ws : List (Fin w → ℤ)) (s : Store)
    (h : Ready n w q ws s) (x : ℤ)
    (hb : ∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ))
    (hr : ∀ a : Fin ws.length, ∀ j : Fin (n+1),
      x ≠ s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(j.val:ℤ)) :
    (run n w q ws.length s).imem x = s.imem x := by
  induction ws generalizing q s with
  | nil => rfl
  | cons f ws ih =>
    rw [List.length_cons,run]
    rw [ih (q+1) (row n w q s) (ready_tail h)]
    · exact row_memory_frame n w q s h.vertices x hb (by simpa using hr ⟨0,by simp⟩)
    · rwa [row_workspace n w q s h.workspace]
    · intro a j
      rw [row_ptr_frame n w q s 2 (by simp)]
      have he : q+1+a.val = q+(a.val+1) := by omega
      rw [he]
      exact hr ⟨a.val+1,by simp⟩ j

lemma row_values {n w q : ℕ} {f : Fin w → ℤ} {ws : List (Fin w → ℤ)} {s : Store}
    (h : Ready n w q (f::ws) s) :
    (∀ v : Fin n, (row n w q s).imem (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(v.val:ℤ)) =
      if ∃ i : Fin w, f i = (v.val+1:ℤ) then 1 else 0) ∧
    (row n w q s).imem (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(n:ℤ)) = s.ptrs 17 := by
  have hh := WordRecord.record_values n (List.ofFn f) q s h.vertices h.count
    (by intro i; simpa using h.encoded ⟨0,by simp⟩ ⟨i.val,by simpa using i.isLt⟩)
    (by intro i v; simpa using h.source_bitmap ⟨0,by simp⟩ ⟨i.val,by simpa using i.isLt⟩ v)
    (h.bitmap_table · ⟨q,by simp⟩ ·)
  have he : (List.ofFn f).length = w := by simp
  rw [he] at hh
  constructor
  · intro v
    simpa only [row_imem,List.mem_ofFn] using hh.2.2.1 v
  · exact hh.2.2.2

/- All catalog rows are retained in order, including duplicate decoded keys. -/
lemma run_values (n w q : ℕ) (ws : List (Fin w → ℤ)) (s : Store) (h : Ready n w q ws s) :
    ∀ a : Fin ws.length,
      (∀ v : Fin n, (run n w q ws.length s).imem
        (s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(v.val:ℤ)) =
          if ∃ i : Fin w, ws[a.val] i = (v.val+1:ℤ) then 1 else 0) ∧
      (run n w q ws.length s).imem
        (s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(n:ℤ)) = s.ptrs 17 := by
  induction ws generalizing q s with
  | nil => intro a; exact Fin.elim0 a
  | cons f ws ih =>
    intro a
    have ht := ready_tail h
    have h2 : (row n w q s).ptrs 2 = s.ptrs 2 := row_ptr_frame _ _ _ _ 2 (by simp)
    have h4 := row_workspace n w q s h.workspace
    by_cases ha : a.val = 0
    · have hword : (f::ws)[a.val] = f := by simpa [ha]
      rw [hword]
      have hh := row_values h
      have hm (j : Fin (n+1)) : (run n w (q+1) ws.length (row n w q s)).imem
          (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) =
          (row n w q s).imem (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) := by
        apply run_memory_frame n w (q+1) ws (row n w q s) ht
        · rw [h4]
          intro v
          exact Ne.symm (h.bitmap_table v ⟨q,by simp⟩ j)
        · intro b k
          rw [h2]
          have hq : (q:ℤ)+1 ≤ ((q+1+b.val:ℕ):ℤ) := by omega
          have hj : (j.val:ℤ) < (n:ℤ)+1 := by have := j.isLt; omega
          have hk : 0 ≤ (k.val:ℤ) := by omega
          have hn : 0 < (n:ℤ)+1 := by omega
          nlinarith
      constructor
      · intro v
        simpa [ha,run,hm ⟨v.val,by omega⟩] using hh.1 v
      · simpa [ha,run,hm ⟨n,by omega⟩] using hh.2
    · let b : Fin ws.length := ⟨a.val-1,by have := a.isLt; simp at this; omega⟩
      have hab : a.val = b.val+1 := by dsimp [b]; omega
      have hword : (f::ws)[a.val] = ws[b.val] := by simp only [hab,List.getElem_cons_succ]
      rw [hword]
      have hh := ih (q+1) (row n w q s) ht b
      have he : q+1+b.val = q+a.val := by omega
      rw [h2,he,row_ptr_frame n w q s 17 (by simp)] at hh
      simpa only [List.length_cons,run,hab,List.getElem_cons_succ] using hh
end StableMSR.Recovery.Compiler.CatalogSweep
set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.CatalogSweep
open ComponentMachine

lemma setup_ready (n w q : ℕ) (ws : List (Fin w → ℤ)) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ)) (hq : s.ptrs 5 = (q:ℤ))
    (hin : ∀ a : Fin ws.length, ∀ i : Fin w,
      s.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ)) = ws[a.val] i)
    (hwb : ∀ a : Fin ws.length, ∀ i : Fin w, ∀ v : Fin n,
      s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ))
    (hwt : ∀ a : Fin ws.length, ∀ i : Fin w, ∀ r : Fin (q+ws.length), ∀ j : Fin (n+1),
      s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) ≠ s.ptrs 2+(r.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ))
    (hbt : ∀ v : Fin n, ∀ r : Fin (q+ws.length), ∀ j : Fin (n+1),
      s.ptrs 4+(v.val:ℤ) ≠ s.ptrs 2+(r.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) :
    Ready n w q ws (setup s) := by
  constructor <;> simp_all [setup,setPtr]

lemma full_values (n w q : ℕ) (ws : List (Fin w → ℤ)) (s : Store)
    (h : Ready n w q ws (setup s)) :
    ∀ a : Fin ws.length,
      (∀ v : Fin n, (fullEval n w q ws.length s).imem
        (s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(v.val:ℤ)) =
          if ∃ i : Fin w, ws[a.val] i = (v.val+1:ℤ) then 1 else 0) ∧
      (fullEval n w q ws.length s).imem
        (s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(n:ℤ)) = s.ptrs 17 := by
  simpa only [fullEval,setup,setPtr,Function.update_of_ne (show (2:ℕ) ≠ 44 by decide),
    Function.update_of_ne (show (2:ℕ) ≠ 45 by decide),Function.update_of_ne (show (2:ℕ) ≠ 46 by decide),
    Function.update_of_ne (show (2:ℕ) ≠ 47 by decide),
    Function.update_of_ne (show (17:ℕ) ≠ 44 by decide),Function.update_of_ne (show (17:ℕ) ≠ 45 by decide),
    Function.update_of_ne (show (17:ℕ) ≠ 46 by decide),Function.update_of_ne (show (17:ℕ) ≠ 47 by decide)]
    using run_values n w q ws (setup s) h

lemma full_memory_frame (n w q : ℕ) (ws : List (Fin w → ℤ)) (s : Store)
    (h : Ready n w q ws (setup s)) (x : ℤ)
    (hb : ∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ))
    (hr : ∀ a : Fin ws.length, ∀ j : Fin (n+1),
      x ≠ s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(j.val:ℤ)) :
    (fullEval n w q ws.length s).imem x = s.imem x := by
  exact run_memory_frame n w q ws (setup s) h x (by simpa [setup,setPtr] using hb)
    (by simpa [setup,setPtr] using hr)

lemma full_old_record (n w q : ℕ) (ws : List (Fin w → ℤ)) (s : Store)
    (h : Ready n w q ws (setup s)) (i : Fin q) (j : Fin (n+1)) :
    (fullEval n w q ws.length s).imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) =
      s.imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) := by
  apply full_memory_frame n w q ws s h
  · intro v
    have hh := h.bitmap_table v ⟨i.val,by have := i.isLt; omega⟩ j
    simpa [setup,setPtr] using Ne.symm hh
  · intro a k
    have hi : (i.val:ℤ)+1 ≤ (q:ℤ) := by have := i.isLt; omega
    have ha : (q:ℤ) ≤ ((q+a.val:ℕ):ℤ) := by omega
    have hj : (j.val:ℤ) < (n:ℤ)+1 := by have := j.isLt; omega
    have hk : 0 ≤ (k.val:ℤ) := by omega
    have hn : 0 < (n:ℤ)+1 := by omega
    nlinarith

lemma full_count (n w q m : ℕ) (s : Store) :
    (fullEval n w q m s).ptrs 5 = s.ptrs 5+(m:ℤ) := by
  rw [fullEval,run_count]; simp [setup,setPtr]
lemma full_cursor (n w q m : ℕ) (s : Store) (hw : s.ptrs 43 = (w:ℤ)) :
    (fullEval n w q m s).ptrs 3 = s.ptrs 3+(m:ℤ)*((w:ℤ)+1) := by
  rw [fullEval,run_cursor]; simp [setup,setPtr,hw]
lemma full_frame (n w q m : ℕ) (s : Store) : DataFrame s (fullEval n w q m s) :=
  run_frame n w q m (setup s)

lemma full_catalog_preserved (n w q : ℕ) (ws : List (Fin w → ℤ)) (s : Store)
    (h : Ready n w q ws (setup s)) (a : Fin ws.length) (i : Fin w) :
    (fullEval n w q ws.length s).imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ)) =
      s.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ)) := by
  apply full_memory_frame n w q ws s h
  · intro v
    simpa [setup,setPtr] using h.source_bitmap a i v
  · intro b j
    have hh := h.source_table a i ⟨q+b.val,by have := b.isLt; omega⟩ j
    simpa [setup,setPtr] using hh

lemma full_base (n w q m : ℕ) (s : Store) : (fullEval n w q m s).ptrs 2 = s.ptrs 2 := by
  rw [fullEval,run_ptr_frame n w q m (setup s) 2 (by simp)]
  simp [setup,setPtr]

/- A single fixed program sweeps an ordinary catalog and constructs every
subset-key record in order, preserving its source and all previous records. -/
end StableMSR.Recovery.Compiler.CatalogSweep

open StableMSR.Recovery.Compiler.CatalogSweep
theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 119 ∧
    ∀ (N n w q : ℕ) (ws : List (Fin w → ℤ)) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (w:ℤ) → s.ptrs 5 = (q:ℤ) →
      s.ptrs 48 = (ws.length:ℤ) →
      (∀ a : Fin ws.length, ∀ i : Fin w,
        s.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ)) = ws[a.val] i) →
      (∀ a : Fin ws.length, ∀ i : Fin w, ∀ v : Fin n,
        s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ)) →
      (∀ a : Fin ws.length, ∀ i : Fin w, ∀ r : Fin (q+ws.length), ∀ j : Fin (n+1),
        s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) ≠ s.ptrs 2+(r.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) →
      (∀ v : Fin n, ∀ r : Fin (q+ws.length), ∀ j : Fin (n+1),
        s.ptrs 4+(v.val:ℤ) ≠ s.ptrs 2+(r.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ steps ≤ ws.length*(4*(q+ws.length)+11*n+11*w+
        (q+ws.length+1)*(11*n+16)+47)+9,
      let result := (MinSumFPT.step P d ω)^[steps] (s.state 0 work)
      result.halted = true ∧ result.work = work+steps ∧
      result.cfg.ptrs 5 = ((q+ws.length:ℕ):ℤ) ∧
      result.cfg.ptrs 3 = s.ptrs 3+(ws.length:ℤ)*((w:ℤ)+1) ∧
      (∀ a : Fin ws.length,
        (∀ v : Fin n, result.imem (s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(v.val:ℤ)) =
          if ∃ i : Fin w, ws[a.val] i = (v.val+1:ℤ) then 1 else 0) ∧
        result.imem (s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(n:ℤ)) = s.ptrs 17) ∧
      (∀ i : Fin q, ∀ j : Fin (n+1),
        result.imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ)) →
        (∀ a : Fin ws.length, ∀ j : Fin (n+1),
          x ≠ s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(j.val:ℤ)) → result.imem x = s.imem x) ∧
      (∀ a : Fin ws.length, ∀ i : Fin w,
        result.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ)) =
          s.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ))) ∧
      result.cfg.ptrs 2 = s.ptrs 2 ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos := by
  refine ⟨program,compile_deterministic fullCmd 0,?_,?_⟩
  · simp [program,compile,fullCmd_size]
  intro N n w q ws d s hn hw hq hm hin hwb hwt hbt ω work
  refine ⟨7+loopCost n w q ws.length,?_,?_⟩
  · have h := loop_cost_bound n w q ws.length
    have he : WordRecord.cost n w (q+ws.length)+4 =
        4*(q+ws.length)+11*n+11*w+(q+ws.length+1)*(11*n+16)+47 := by rfl
    rw [he] at h
    omega
  dsimp only
  rw [machine_execution d n w q ws.length s hn hw hq hm ω work]
  have h := setup_ready n w q ws s hn hw hq hin hwb hwt hbt
  have hf := full_frame n w q ws.length s
  refine ⟨rfl,rfl,?_,full_cursor n w q ws.length s hw,full_values n w q ws s h,
    full_old_record n w q ws s h,full_memory_frame n w q ws s h,
    full_catalog_preserved n w q ws s h,full_base n w q ws.length s,
    hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩
  change (fullEval n w q ws.length s).ptrs 5 = _
  rw [full_count,hq]; push_cast; rfl
