-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.WordBitmap.word_bitmap_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-15T19:00:23.512161+00:00
-- url     : https://prove2.me/submissions/1f154ad0-bc6f-4866-a52e-9dfc70f2a198

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
end StableMSR.Recovery.Compiler.WordBitmap

open StableMSR.Recovery.Compiler.WordBitmap
theorem solution :
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
