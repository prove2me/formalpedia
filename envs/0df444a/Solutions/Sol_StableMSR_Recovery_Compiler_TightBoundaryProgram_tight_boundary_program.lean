-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.TightBoundaryProgram.tight_boundary_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-15T01:32:10.741903+00:00
-- url     : https://prove2.me/submissions/1c9bcbe0-0685-44cd-bfd9-5f7485b3967c

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

set_option autoImplicit false
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

set_option autoImplicit false
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

namespace StableMSR.Recovery.Compiler.ComponentInit

open BitmapFill TupleWriter ComponentMemory

/- Initialize constants and the inclusive bounds of the reached bitmap. -/
def prepCmd : Cmd :=
  .seq (.atom (.pointerConst 0 0))
    (.seq (.atom (.pointerConst 1 1))
      (.seq (.atom (.pointerCopy 15 4))
        (.seq (.atom (.pointerAdd 16 4 6)) (.atom (.pointerDec 16)))))

def prepEval (s : Store) : Store :=
  { s with ptrs := (Function.update
      (Function.update (Function.update (Function.update s.ptrs 0 0) 1 1) 15 (s.ptrs 4))
      16 (s.ptrs 4 + s.ptrs 6 - 1)) }

/- Mark the seed after zero-filling all reached cells. -/
def seedCmd : Cmd :=
  .seq (.atom (.pointerAdd 15 4 17)) (.atom (.integerStore 15 1))

def seedEval (s : Store) : Store :=
  { s with
    ptrs := Function.update s.ptrs 15 (s.ptrs 4 + s.ptrs 17)
    imem := Function.update s.imem (s.ptrs 4 + s.ptrs 17) (s.ptrs 1) }

/- Fixed initialization code; the vertex count is read from pointer register 6. -/
def initCmd : Cmd := .seq prepCmd (.seq (fillCmd 15 16 0) seedCmd)

def initEval (q : ℕ) (s : Store) : Store :=
  seedEval (fillEval 15 0 q (prepEval s))

@[simp] lemma initCmd_size : initCmd.size = 12 := rfl

lemma prep_exec {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    Executes d prepCmd s (prepEval s) 5 := by
  have h := Executes.seq (Executes.atom (.pointerConst 0 0) (d := d) s)
    (Executes.seq (Executes.atom (.pointerConst 1 1) (d := d) _)
      (Executes.seq (Executes.atom (.pointerCopy 15 4) (d := d) _)
        (Executes.seq (Executes.atom (.pointerAdd 16 4 6) (d := d) _)
          (Executes.atom (.pointerDec 16) (d := d) _))))
  simpa [prepCmd,prepEval,Op.eval,Function.update_idem] using h

lemma seed_exec {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    Executes d seedCmd s (seedEval s) 2 := by
  have h := Executes.seq (Executes.atom (.pointerAdd 15 4 17) (d := d) s)
    (Executes.atom (.integerStore 15 1) (d := d) _)
  simpa [seedCmd,seedEval,Op.eval] using h

lemma init_exec {n : ℕ} (d : Point n → Point n → ℝ)
    (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    Executes d initCmd s (initEval q s) (4*q+9) := by
  have hstop : (prepEval s).ptrs 16 = (prepEval s).ptrs 15 + (q : ℤ) - 1 := by
    simp [prepEval,hcount]
  have hf := fill_exec d 15 16 0 q (prepEval s) (by decide) hstop
  have h := Executes.seq (prep_exec d s)
    (Executes.seq hf (seed_exec d (fillEval 15 0 q (prepEval s))))
  simpa only [initCmd,initEval,show 5+(4*q+2+2)=4*q+9 by omega] using h

lemma init_ptr_ne (q j : ℕ) (s : Store)
    (h0 : j ≠ 0) (h1 : j ≠ 1) (h15 : j ≠ 15) (h16 : j ≠ 16) :
    (initEval q s).ptrs j = s.ptrs j := by
  simp only [initEval,seedEval,Function.update_of_ne h15]
  rw [fill_ptr_ne 15 0 q j (prepEval s) h15]
  simp [prepEval,h0,h1,h15,h16]

@[simp] lemma init_ptr_zero (q : ℕ) (s : Store) : (initEval q s).ptrs 0 = 0 := by
  simp only [initEval,seedEval,Function.update_of_ne (show (0 : ℕ) ≠ 15 by decide)]
  rw [fill_ptr_ne 15 0 q 0 (prepEval s) (by decide)]
  simp [prepEval]

@[simp] lemma init_ptr_one (q : ℕ) (s : Store) : (initEval q s).ptrs 1 = 1 := by
  simp only [initEval,seedEval,Function.update_of_ne (show (1 : ℕ) ≠ 15 by decide)]
  rw [fill_ptr_ne 15 0 q 1 (prepEval s) (by decide)]
  simp [prepEval]

lemma init_frame (q : ℕ) (s : Store) :
    (initEval q s).regs = s.regs ∧
    (initEval q s).mem = s.mem ∧
    (initEval q s).queries = s.queries ∧
    (initEval q s).tapePos = s.tapePos ∧
    (initEval q s).output = s.output :=
  fill_frame 15 0 q (prepEval s)

lemma init_memory (q : ℕ) (s : Store) :
    (initEval q s).imem =
      Function.update (writeMemory (s.ptrs 4) (List.replicate q (0 : ℤ)) s.imem)
        (s.ptrs 4 + s.ptrs 17) 1 := by
  simp only [initEval,seedEval]
  rw [fill_memory 15 0 q (prepEval s) (by decide),
    fill_ptr_ne 15 0 q 4 (prepEval s) (by decide),
    fill_ptr_ne 15 0 q 17 (prepEval s) (by decide),
    fill_ptr_ne 15 0 q 1 (prepEval s) (by decide)]
  simp [prepEval]

lemma init_bitmap {n : ℕ} (s : Store) (seed : Fin n)
    (hseed : s.ptrs 17 = (seed.val : ℤ)) :
    Bitmap (initEval n s).imem (s.ptrs 4) {seed} := by
  intro v
  rw [init_memory,hseed]
  by_cases hv : v = seed
  · subst v
    simp [address]
  · have haddr : address (s.ptrs 4) v ≠ s.ptrs 4 + (seed.val : ℤ) := by
      change address (s.ptrs 4) v ≠ address (s.ptrs 4) seed
      exact fun h => hv ((address_eq_iff _ _ _).mp h)
    rw [Function.update_of_ne haddr]
    have hi : v.val < (List.replicate n (0 : ℤ)).length := by simpa using v.isLt
    rw [address,writeMemory_get _ _ _ v.val hi]
    simp [hv]

lemma init_memory_frame {n : ℕ} (s : Store) (seed : Fin n)
    (hseed : s.ptrs 17 = (seed.val : ℤ)) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (initEval n s).imem x = s.imem x := by
  have hs : x ≠ s.ptrs 4 + (seed.val : ℤ) := hx seed
  rw [init_memory,hseed,Function.update_of_ne hs]
  by_cases hlo : x < s.ptrs 4
  · exact writeMemory_before _ _ _ _ hlo
  · have hhi : s.ptrs 4 + (n : ℤ) ≤ x := by
      by_contra hbad
      have hnonneg : 0 ≤ x - s.ptrs 4 := by omega
      have hlt : (x - s.ptrs 4).toNat < n := by omega
      let v : Fin n := ⟨(x - s.ptrs 4).toNat,hlt⟩
      have he : x = address (s.ptrs 4) v := by
        dsimp [address,v]
        omega
      exact hx v he
    apply writeMemory_after
    simpa only [List.length_replicate] using hhi

lemma init_preserves_bitmap {n : ℕ} (s : Store) (seed : Fin n)
    (hseed : s.ptrs 17 = (seed.val : ℤ)) (base : ℤ) (A : Finset (Fin n))
    (hsep : Separate (n := n) base (s.ptrs 4)) (hA : Bitmap s.imem base A) :
    Bitmap (initEval n s).imem base A := by
  intro v
  rw [init_memory_frame s seed hseed _ (fun w => hsep v w)]
  exact hA v

lemma init_preserves_edges {n : ℕ} (s : Store) (seed : Fin n)
    (hseed : s.ptrs 17 = (seed.val : ℤ)) (edgeBase : ℤ)
    (es : List (Fin n × Fin n))
    (hsep : EdgesSeparate edgeBase (s.ptrs 4) es)
    (hedges : EdgeEncoding s.imem edgeBase es) :
    EdgeEncoding (initEval n s).imem edgeBase es := by
  intro j hj
  rw [init_memory_frame s seed hseed _ (fun v => (hsep j hj v).1),
    init_memory_frame s seed hseed _ (fun v => (hsep j hj v).2)]
  exact hedges j hj

end StableMSR.Recovery.Compiler.ComponentInit



namespace StableMSR.Recovery.BoundaryMemory
open ComponentMemory

/- A graph's external neighborhood of a specified vertex set. -/
noncomputable def externalBoundary {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => v ∉ C ∧ ∃ u ∈ C, G.Adj u v)

@[simp] theorem mem_externalBoundary {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (v : Fin n) :
    v ∈ externalBoundary G C ↔ v ∉ C ∧ ∃ u ∈ C, G.Adj u v := by
  classical
  simp [externalBoundary]

/- Pure processing of one directed arc for an immutable source set. -/
def boundaryRelax {n : ℕ} (C B : Finset (Fin n)) (e : Fin n × Fin n) : Finset (Fin n) :=
  if e.1 ∈ C ∧ e.2 ∉ C then insert e.2 B else B

/- One finite-set scan suffices because membership in the source set never changes. -/
def boundarySetPass {n : ℕ} (C : Finset (Fin n))
    (es : List (Fin n × Fin n)) (B : Finset (Fin n)) : Finset (Fin n) :=
  es.foldl (boundaryRelax C) B

 theorem mem_boundarySetPass {n : ℕ} (C : Finset (Fin n))
    (es : List (Fin n × Fin n)) (B : Finset (Fin n)) (v : Fin n) :
    v ∈ boundarySetPass C es B ↔
      v ∈ B ∨ (v ∉ C ∧ ∃ u, (u, v) ∈ es ∧ u ∈ C) := by
  induction es generalizing B with
  | nil => simp [boundarySetPass]
  | cons e es ih =>
    change v ∈ boundarySetPass C es (boundaryRelax C B e) ↔ _
    rw [ih]
    rcases e with ⟨u, w⟩
    by_cases h : u ∈ C ∧ w ∉ C
    · simp only [boundaryRelax, h, if_true, Finset.mem_insert, List.mem_cons,
        Prod.mk.injEq]
      aesop
    · simp only [boundaryRelax, h, if_false, List.mem_cons, Prod.mk.injEq]
      aesop

/- No ordering or uniqueness condition is imposed on the directed edge list. -/
theorem boundarySetPass_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    boundarySetPass C es ∅ = externalBoundary G C := by
  ext v
  rw [mem_boundarySetPass, mem_externalBoundary]
  simp only [Finset.notMem_empty, false_or]
  constructor
  · rintro ⟨hv, u, he, hu⟩
    exact ⟨hv, u, hu, hsound (u, v) he⟩
  · rintro ⟨hv, u, hu, huv⟩
    exact ⟨hv, u, hcomplete u v huv, hu⟩

/- Memory effect of one boundary-marking interpreter step. -/
def boundaryMark (Cbase Bbase u v : ℤ) (mem : ℤ → ℤ) : ℤ → ℤ :=
  if 0 < mem (Cbase + u) ∧ mem (Cbase + v) ≤ 0 then
    Function.update mem (Bbase + v) 1
  else mem

/- Memory effect of one full directed-edge scan. -/
def boundaryPass {n : ℕ} (Cbase Bbase : ℤ)
    (es : List (Fin n × Fin n)) (mem : ℤ → ℤ) : ℤ → ℤ :=
  es.foldl (fun m e => boundaryMark Cbase Bbase e.1.val e.2.val m) mem

 theorem boundaryMark_frame (Cbase Bbase u v : ℤ) (mem : ℤ → ℤ)
    (x : ℤ) (hx : x ≠ Bbase + v) :
    boundaryMark Cbase Bbase u v mem x = mem x := by
  simp only [boundaryMark]
  split
  · exact Function.update_of_ne hx _ _
  · rfl

 theorem boundaryMark_bitmap {n : ℕ} {mem : ℤ → ℤ}
    {Cbase Bbase : ℤ} {C B : Finset (Fin n)}
    (hC : Bitmap mem Cbase C) (hB : Bitmap mem Bbase B)
    (e : Fin n × Fin n) :
    Bitmap (boundaryMark Cbase Bbase e.1.val e.2.val mem) Bbase
      (boundaryRelax C B e) := by
  intro x
  have hsource := hC e.1
  have htarget := hC e.2
  dsimp [address] at hsource htarget
  by_cases hu : e.1 ∈ C <;> by_cases hv : e.2 ∈ C
  · simp [boundaryMark, hsource, htarget, hu, hv, boundaryRelax, hB x]
  · simp only [hu, hv, if_true, if_false] at hsource htarget
    simp only [boundaryMark, hsource, htarget, zero_lt_one, le_refl, and_self, if_true,
      boundaryRelax, hu, hv, not_false_eq_true, and_self, if_true]
    by_cases hx : x = e.2
    · subst x
      simp [address]
    · have haddr : address Bbase x ≠ Bbase + (e.2.val : ℤ) := by
        change address Bbase x ≠ address Bbase e.2
        exact fun h => hx ((address_eq_iff Bbase x e.2).mp h)
      rw [Function.update_of_ne haddr]
      simpa [hx] using hB x
  · simp [boundaryMark, hsource, htarget, hu, hv, boundaryRelax, hB x]
  · simp [boundaryMark, hsource, htarget, hu, hv, boundaryRelax, hB x]

 theorem boundaryMark_preserves_bitmap {n : ℕ} {mem : ℤ → ℤ}
    {Cbase Bbase : ℤ} {C : Finset (Fin n)}
    (hsep : Separate (n := n) Cbase Bbase)
    (hC : Bitmap mem Cbase C) (e : Fin n × Fin n) :
    Bitmap (boundaryMark Cbase Bbase e.1.val e.2.val mem) Cbase C := by
  intro x
  rw [boundaryMark_frame Cbase Bbase _ _ mem _ (hsep x e.2)]
  exact hC x

 theorem boundaryPass_refines {n : ℕ} {mem : ℤ → ℤ}
    {Cbase Bbase : ℤ} {C B : Finset (Fin n)}
    (hsep : Separate (n := n) Cbase Bbase)
    (hC : Bitmap mem Cbase C) (hB : Bitmap mem Bbase B)
    (es : List (Fin n × Fin n)) :
    Bitmap (boundaryPass Cbase Bbase es mem) Cbase C ∧
    Bitmap (boundaryPass Cbase Bbase es mem) Bbase (boundarySetPass C es B) := by
  induction es generalizing mem B with
  | nil => exact ⟨hC, hB⟩
  | cons e es ih =>
    exact ih (boundaryMark_preserves_bitmap hsep hC e) (boundaryMark_bitmap hC hB e)

 theorem boundaryPass_frame {n : ℕ} (Cbase Bbase : ℤ)
    (es : List (Fin n × Fin n)) (mem : ℤ → ℤ) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address Bbase v) :
    boundaryPass Cbase Bbase es mem x = mem x := by
  induction es generalizing mem with
  | nil => rfl
  | cons e es ih =>
    change boundaryPass Cbase Bbase es
      (boundaryMark Cbase Bbase e.1.val e.2.val mem) x = mem x
    rw [ih]
    exact boundaryMark_frame _ _ _ _ _ _ (hx e.2)

 theorem boundaryPass_preserves_edges {n : ℕ} {mem : ℤ → ℤ}
    (Cbase Bbase edgeBase : ℤ) (xs es : List (Fin n × Fin n))
    (hsep : EdgesSeparate edgeBase Bbase es)
    (hencode : EdgeEncoding mem edgeBase es) :
    EdgeEncoding (boundaryPass Cbase Bbase xs mem) edgeBase es := by
  intro j hj
  rw [boundaryPass_frame _ _ _ _ _ (fun v => (hsep j hj v).1),
      boundaryPass_frame _ _ _ _ _ (fun v => (hsep j hj v).2)]
  exact hencode j hj

/- One pass from the empty output bitmap computes the exact external boundary. -/
theorem boundaryPass_boundary {n : ℕ} {mem : ℤ → ℤ} {Cbase Bbase : ℤ}
    (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (es : List (Fin n × Fin n))
    (hsep : Separate (n := n) Cbase Bbase)
    (hC : Bitmap mem Cbase C) (hB : Bitmap (n := n) mem Bbase ∅)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    Bitmap (boundaryPass Cbase Bbase es mem) Cbase C ∧
    Bitmap (boundaryPass Cbase Bbase es mem) Bbase (externalBoundary G C) := by
  simpa only [boundarySetPass_eq G C es hsound hcomplete] using
    boundaryPass_refines hsep hC hB es

/- Exact positive-flag readback, without a set-valued output oracle. -/
theorem boundaryPass_positive_iff {n : ℕ} {mem : ℤ → ℤ} {Cbase Bbase : ℤ}
    (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (es : List (Fin n × Fin n))
    (hsep : Separate (n := n) Cbase Bbase)
    (hC : Bitmap mem Cbase C) (hB : Bitmap (n := n) mem Bbase ∅)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) (v : Fin n) :
    0 < boundaryPass Cbase Bbase es mem (address Bbase v) ↔
      v ∉ C ∧ ∃ u ∈ C, G.Adj u v := by
  rw [(boundaryPass_boundary G C es hsep hC hB hsound hcomplete).2 v]
  by_cases hv : v ∈ externalBoundary G C
  · simpa only [hv, if_true, zero_lt_one, true_iff] using
      (mem_externalBoundary G C v).mp hv
  · simp only [hv, if_false, lt_self_iff_false, false_iff]
    exact fun h => hv ((mem_externalBoundary G C v).mpr h)

end StableMSR.Recovery.BoundaryMemory



open scoped Classical
namespace StableMSR.Recovery.Compiler.BoundaryMachine
open ComponentMachine

/- Mark the target outside C when the source lies in C. Padding charges five
steps in all cases, including every conditional branch. -/
def markCmd : Cmd :=
  .ite (.pointerLE 13 0) pad4
    (.ite (.pointerLE 14 0) (.seq (.atom (.integerStore 11 1)) nop) nop)

noncomputable def markEval (s : Store) : Store :=
  if s.ptrs 13 ≤ s.ptrs 0 then s else
  if s.ptrs 14 ≤ s.ptrs 0 then
    { s with imem := Function.update s.imem (s.ptrs 11) (s.ptrs 1) }
  else s

lemma mark_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d markCmd s (markEval s) 5 := by
  by_cases h13 : s.ptrs 13 ≤ s.ptrs 0
  · simpa [markCmd, markEval, h13] using
      Executes.ite_true (c := Cond.pointerLE 13 0)
        (no := Cmd.ite (.pointerLE 14 0) (.seq (.atom (.integerStore 11 1)) nop) nop)
        h13 (pad4_exec d s)
  · by_cases h14 : s.ptrs 14 ≤ s.ptrs 0
    · simpa [markCmd, markEval, h13, h14, Op.eval] using
        Executes.ite_false (c := Cond.pointerLE 13 0) (yes := pad4) h13
          (Executes.ite_true (c := Cond.pointerLE 14 0) (no := nop) h14
            (Executes.seq (Executes.atom (.integerStore 11 1) s)
              (nop_exec d (Op.eval d (.integerStore 11 1) s))))
    · simpa [markCmd, markEval, h13, h14] using
        Executes.ite_false (c := Cond.pointerLE 13 0) (yes := pad4) h13
          (Executes.ite_false (c := Cond.pointerLE 14 0)
            (yes := Cmd.seq (.atom (.integerStore 11 1)) nop) h14 (nop_exec d s))

def edgeOps : List Op :=
  [.integerLoad 10 7, .pointerInc 7, .integerLoad 11 7, .pointerInc 7,
   .pointerAdd 10 3 10, .pointerAdd 12 3 11, .pointerAdd 11 4 11,
   .integerLoad 13 10, .integerLoad 14 12]

def edgeCmd : Cmd := .seq (opsCmd edgeOps) (.seq markCmd (.atom (.pointerInc 8)))

noncomputable def edgeInput (s : Store) : Store :=
  let a := s.imem (s.ptrs 7)
  let b := s.imem (s.ptrs 7+1)
  let t := setPtr (setPtr (setPtr (setPtr s 7 (s.ptrs 7+2))
    10 (s.ptrs 3+a)) 12 (s.ptrs 3+b)) 11 (s.ptrs 4+b)
  setPtr (setPtr t 13 (s.imem (s.ptrs 3+a))) 14 (s.imem (s.ptrs 3+b))

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

lemma edge_frame (s : Store) : DataFrame s (edgeStep s) := by
  unfold edgeStep incPtr setPtr markEval
  split <;> (try split) <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma pass_frame (m : ℕ) (s : Store) : DataFrame s (passEval m s) :=
  (show DataFrame s (passSetup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame edgeStep edge_frame m (passSetup s))

lemma pass_size : passCmd.size = 26 := by decide

end StableMSR.Recovery.Compiler.BoundaryMachine


namespace StableMSR.Recovery.Compiler.BoundaryMachine
open StableMSR.Recovery.ComponentMemory
open StableMSR.Recovery.BoundaryMemory
open ComponentMachine

/- The actual read/branch/store step has precisely the abstract marking effect. -/
theorem edgeStep_imem (s : Store) (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1) :
    (edgeStep s).imem =
      boundaryMark (s.ptrs 3) (s.ptrs 4) (s.imem (s.ptrs 7))
        (s.imem (s.ptrs 7 + 1)) s.imem := by
  simp [edgeStep, incPtr, setPtr, markEval, edgeInput, boundaryMark, h0, h1]
  split <;> (try split) <;> simp_all <;> omega

 theorem edge_low (s : Store) (j : ℕ) (hj : j < 7) :
    (edgeStep s).ptrs j = s.ptrs j :=
  edge_ptr_frame s j (by omega)

 theorem encoding_tail {n : ℕ} {mem : ℤ → ℤ} {base : ℤ}
    {e : Fin n × Fin n} {es : List (Fin n × Fin n)}
    (h : EdgeEncoding mem base (e :: es)) : EdgeEncoding mem (base + 2) es := by
  intro j hj
  have h' := h (j + 1) (by simpa using Nat.succ_lt_succ hj)
  simpa [List.getElem_cons_succ, Nat.cast_add, Nat.cast_one,
    mul_add, add_assoc, add_comm, add_left_comm] using h'

 theorem separation_tail {n : ℕ} {base reachedBase : ℤ}
    {e : Fin n × Fin n} {es : List (Fin n × Fin n)}
    (h : EdgesSeparate base reachedBase (e :: es)) :
    EdgesSeparate (base + 2) reachedBase es := by
  intro j hj v
  have h' := h (j + 1) (by simpa using Nat.succ_lt_succ hj) v
  simpa [Nat.cast_add, Nat.cast_one, mul_add, add_assoc, add_comm, add_left_comm] using h'

/- Sequentially executing the edge step follows the input list exactly, while
writes to the reached bitmap leave all future endpoint reads unchanged. -/
theorem edgeSteps_imem {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 7) es)
    (hsep : EdgesSeparate (s.ptrs 7) (s.ptrs 4) es) :
    (edgeStep^[es.length] s).imem =
      boundaryPass (s.ptrs 3) (s.ptrs 4) es s.imem := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    have hh := hencode 0 (by simp)
    simp only [Nat.cast_zero, mul_zero, add_zero, List.getElem_cons_zero] at hh
    have hm : (edgeStep s).imem =
        boundaryMark (s.ptrs 3) (s.ptrs 4) e.1.val e.2.val s.imem := by
      simpa only [hh.1, hh.2] using edgeStep_imem s h0 h1
    have he : EdgeEncoding (edgeStep s).imem (s.ptrs 7) (e :: es) := by
      rw [hm]
      exact boundaryPass_preserves_edges (s.ptrs 3) (s.ptrs 4) (s.ptrs 7)
        [e] (e :: es) hsep hencode
    have htail : EdgeEncoding (edgeStep s).imem ((edgeStep s).ptrs 7) es := by
      rw [edge_cursor]
      exact encoding_tail he
    have htailsep : EdgesSeparate ((edgeStep s).ptrs 7) ((edgeStep s).ptrs 4) es := by
      rw [edge_cursor, edge_low s 4 (by omega)]
      exact separation_tail hsep
    rw [List.length_cons, Function.iterate_succ_apply]
    rw [ih (edgeStep s) (by rw [edge_low s 0 (by omega), h0])
      (by rw [edge_low s 1 (by omega), h1]) htail htailsep]
    rw [edge_low s 3 (by omega), edge_low s 4 (by omega), hm]
    rfl

/- A complete interpreter scan refines the finite-set scan's memory fold. -/
theorem passEval_imem {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) :
    (passEval es.length s).imem =
      boundaryPass (s.ptrs 3) (s.ptrs 4) es s.imem := by
  apply edgeSteps_imem es (passSetup s)
    (by simpa [passSetup, setPtr] using h0)
    (by simpa [passSetup, setPtr] using h1)
    (by simpa [passSetup, setPtr] using hencode)
    (by simpa [passSetup, setPtr] using hsep)


/- The interpreter scan computes the exact external-boundary bitmap from a
zeroed output, and preserves the input component bitmap. -/
theorem passEval_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hedges : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hC : Bitmap s.imem (s.ptrs 3) C) (hB : Bitmap (n := n) s.imem (s.ptrs 4) ∅)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    Bitmap (passEval es.length s).imem (s.ptrs 3) C ∧
    Bitmap (passEval es.length s).imem (s.ptrs 4) (externalBoundary G C) := by
  rw [passEval_imem es s h0 h1 hencode hedges]
  exact boundaryPass_boundary G C es hsep hC hB hsound hcomplete

/- Every integer cell outside the writable output bitmap is unchanged. -/
theorem passEval_imem_frame {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (passEval es.length s).imem x = s.imem x := by
  rw [passEval_imem es s h0 h1 hencode hsep]
  exact boundaryPass_frame _ _ _ _ _ hx

end StableMSR.Recovery.Compiler.BoundaryMachine



open scoped Classical
namespace StableMSR.Recovery.Compiler.BoundaryProgram
open ComponentInit ComponentMachine BitmapFill ComponentMemory BoundaryMemory

/- Clear the output bitmap and initialize the zero/one constants. -/
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

lemma clear_preserves_bitmap {n : ℕ} (s : Store) (base : ℤ) (C : Finset (Fin n))
    (hsep : Separate (n := n) base (s.ptrs 4)) (hC : Bitmap s.imem base C) :
    Bitmap (clearEval n s).imem base C := by
  intro v
  rw [clear_memory_frame n s _ (fun w => hsep v w)]
  exact hC v

lemma clear_preserves_edges {n : ℕ} (s : Store) (edgeBase : ℤ)
    (es : List (Fin n × Fin n)) (hsep : EdgesSeparate edgeBase (s.ptrs 4) es)
    (he : EdgeEncoding s.imem edgeBase es) :
    EdgeEncoding (clearEval n s).imem edgeBase es := by
  intro j hj
  rw [clear_memory_frame n s _ (fun v => (hsep j hj v).1),
    clear_memory_frame n s _ (fun v => (hsep j hj v).2)]
  exact he j hj

def fullCmd : Cmd := .seq clearCmd BoundaryMachine.passCmd
noncomputable def fullEval (n m : ℕ) (s : Store) : Store :=
  BoundaryMachine.passEval m (clearEval n s)
noncomputable def program : MinSumFPT.Program := compile fullCmd 0

lemma fullCmd_size : fullCmd.size = 36 := by decide
lemma program_length : program.length = 37 := by
  simp [program,compile,compileAt_length,fullCmd_size]

lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d fullCmd s (fullEval n m s) (4*n+17*m+11) := by
  have h := Executes.seq (clear_exec d n s hn)
    (BoundaryMachine.pass_exec d m (clearEval n s)
      (by rw [clear_ptr_ne n s 5 (by decide) (by decide) (by decide) (by decide),hm]))
  convert h using 1 <;> try rfl
  omega

lemma full_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (n m : ℕ) (s : Store) (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[4*n+17*m+12] (s.state 0 work) =
      (fullEval n m s).haltedState 36 (work+(4*n+17*m+12)) 0 := by
  simpa [program,fullCmd_size,Nat.add_assoc] using
    compile_halts (full_exec d n m s hm hn) ω work 0

lemma fullEval_frame (n m : ℕ) (s : Store) : DataFrame s (fullEval n m s) :=
  (clear_frame n s).trans (BoundaryMachine.pass_frame m (clearEval n s))

lemma fullEval_ptr_frame (n m : ℕ) (s : Store) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ 6 ∨ 16 < j) : (fullEval n m s).ptrs j = s.ptrs j := by
  unfold fullEval
  rw [BoundaryMachine.pass_ptr_frame m (clearEval n s) j (by omega)]
  exact clear_ptr_ne n s j (by omega) (by omega) (by omega) (by omega)

lemma fullEval_imem {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) :
    (fullEval n es.length s).imem =
      boundaryPass (s.ptrs 3) (s.ptrs 4) es (clearEval n s).imem := by
  have hp (j : ℕ) (h2 : 2 ≤ j) (h6 : j ≤ 6) :
      (clearEval n s).ptrs j = s.ptrs j :=
    clear_ptr_ne n s j (by omega) (by omega) (by omega) (by omega)
  have he' : EdgeEncoding (clearEval n s).imem ((clearEval n s).ptrs 2) es := by
    rw [hp 2 (by omega) (by omega)]
    exact clear_preserves_edges s _ es hesep he
  have hs' : EdgesSeparate ((clearEval n s).ptrs 2) ((clearEval n s).ptrs 4) es := by
    rwa [hp 2 (by omega) (by omega),hp 4 (by omega) (by omega)]
  unfold fullEval
  rw [BoundaryMachine.passEval_imem es (clearEval n s)
      (clear_constants n s).1 (clear_constants n s).2 he' hs',
    hp 3 (by omega) (by omega),hp 4 (by omega) (by omega)]

lemma fullEval_boundary {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n))
    (es : List (Fin n × Fin n)) (s : Store)
    (hC : Bitmap s.imem (s.ptrs 3) C)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Bitmap (fullEval n es.length s).imem (s.ptrs 3) C ∧
    Bitmap (fullEval n es.length s).imem (s.ptrs 4) (externalBoundary G C) := by
  rw [fullEval_imem es s he hesep]
  exact boundaryPass_boundary G C es hsep
    (clear_preserves_bitmap s _ C hsep hC) (clear_bitmap n s) hsound hcomplete

lemma fullEval_imem_frame {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (fullEval n es.length s).imem x = s.imem x := by
  rw [fullEval_imem es s he hesep,boundaryPass_frame _ _ _ _ _ hx]
  exact clear_memory_frame n s x hx

lemma fullEval_boundary_bitmap {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hC : Bitmap s.imem (s.ptrs 3) C)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) (v : Fin n) :
    (fullEval n es.length s).imem (address (s.ptrs 4) v) =
      if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0 := by
  simpa only [mem_externalBoundary] using
    (fullEval_boundary G C es s hC he hsep hesep hsound hcomplete).2 v

/- One dimension-independent finite program clears its output and computes
the exact external neighborhood in 4n+17m+12 charged instructions. -/
theorem boundary_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 37 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) →
      Bitmap s.imem (s.ptrs 3) C → EdgeEncoding s.imem (s.ptrs 2) es →
      Separate (n := n) (s.ptrs 3) (s.ptrs 4) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let result := (MinSumFPT.step P d ω)^[4*n+17*es.length+12] (s.state 0 work)
      result.halted = true ∧ result.work = work+(4*n+17*es.length+12) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧
      (∀ v : Fin n, result.imem (address (s.ptrs 4) v) =
        if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ 6 → result.cfg.ptrs j = s.ptrs j) := by
  refine ⟨program,compile_deterministic fullCmd 0,program_length,?_⟩
  intro n d G C es s hm hn hC he hsep hesep hsound hcomplete ω work
  dsimp only
  rw [full_machine_execution d n es.length s hm hn ω work]
  have hf := fullEval_frame n es.length s
  refine ⟨rfl,rfl,hf.2.2.1,hf.2.2.2.1,hf.2.1,hf.1,
    fullEval_boundary_bitmap G C es s hC he hsep hesep hsound hcomplete,
    fullEval_imem_frame es s he hesep,?_⟩
  intro j h2 h6
  exact fullEval_ptr_frame n es.length s j (Or.inl ⟨h2,h6⟩)

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
namespace StableMSR.Recovery.Compiler.TightBoundaryProgram
open ComponentMemory ComponentMachine

/- Preserve the input-set base before comparing the candidate set with
the newly constructed boundary bitmap. -/
def redirectCmd : Cmd :=
  .seq (.atom (.pointerCopy 24 3)) (.atom (.pointerCopy 3 17))

def redirect (s : Store) : Store :=
  { s with ptrs := Function.update (Function.update s.ptrs 24 (s.ptrs 3)) 3 (s.ptrs 17) }

def restoreCmd : Cmd := .atom (.pointerCopy 3 24)
def restore (s : Store) : Store :=
  { s with ptrs := Function.update s.ptrs 3 (s.ptrs 24) }

lemma redirect_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d redirectCmd s (redirect s) 2 := by
  have h := Executes.seq (Executes.atom (.pointerCopy 24 3) (d := d) s)
    (Executes.atom (.pointerCopy 3 17) (d := d) _)
  simpa [redirectCmd,redirect,Op.eval] using h

lemma restore_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d restoreCmd s (restore s) 1 :=
  Executes.atom (.pointerCopy 3 24) s

@[simp] lemma redirect_imem (s : Store) : (redirect s).imem = s.imem := rfl
@[simp] lemma restore_imem (s : Store) : (restore s).imem = s.imem := rfl
@[simp] lemma redirect_ptr3 (s : Store) : (redirect s).ptrs 3 = s.ptrs 17 := by
  simp [redirect]
@[simp] lemma redirect_ptr24 (s : Store) : (redirect s).ptrs 24 = s.ptrs 3 := by
  simp [redirect]
lemma redirect_ptr_ne (s : Store) (j : ℕ) (h3 : j ≠ 3) (h24 : j ≠ 24) :
    (redirect s).ptrs j = s.ptrs j := by simp [redirect,h3,h24]
lemma restore_ptr_ne (s : Store) (j : ℕ) (h3 : j ≠ 3) :
    (restore s).ptrs j = s.ptrs j := by simp [restore,h3]

/- Compose the verified commands, with one final halt only. -/
def fullCmd : Cmd := .seq BoundaryProgram.fullCmd
  (.seq redirectCmd (.seq ArrayEquality.equalityCmd restoreCmd))
noncomputable def fullEval (n m : ℕ) (s : Store) : Store :=
  restore (ArrayEquality.equalityEval n (redirect (BoundaryProgram.fullEval n m s)))
noncomputable def program : MinSumFPT.Program := compile fullCmd 0

lemma fullCmd_size : fullCmd.size = 60 := by decide
lemma program_length : program.length = 61 := by
  simp [program,compile,compileAt_length,fullCmd_size]

lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d fullCmd s (fullEval n m s) (15*n+17*m+20) := by
  have hc : (redirect (BoundaryProgram.fullEval n m s)).ptrs 6 = (n:ℤ) := by
    rw [redirect_ptr_ne _ 6 (by decide) (by decide)]
    rw [BoundaryProgram.fullEval_ptr_frame n m s 6 (by omega),hn]
  have h := Executes.seq (BoundaryProgram.full_exec d n m s hm hn)
    (Executes.seq (redirect_exec d _)
      (Executes.seq (ArrayEquality.equality_exec d n _ hc) (restore_exec d _)))
  convert h using 1 <;> try rfl
  omega

lemma full_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (n m : ℕ) (s : Store) (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[15*n+17*m+21] (s.state 0 work) =
      (fullEval n m s).haltedState 60 (work+(15*n+17*m+21)) 0 := by
  simpa [program,fullCmd_size,Nat.add_assoc] using
    compile_halts (full_exec d n m s hm hn) ω work 0

lemma fullEval_frame (n m : ℕ) (s : Store) : DataFrame s (fullEval n m s) := by
  have h := ArrayEquality.equality_frame n (redirect (BoundaryProgram.fullEval n m s))
  exact (BoundaryProgram.fullEval_frame n m s).trans
    ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

lemma fullEval_imem (n m : ℕ) (s : Store) :
    (fullEval n m s).imem = (BoundaryProgram.fullEval n m s).imem :=
  (ArrayEquality.equality_frame n (redirect (BoundaryProgram.fullEval n m s))).2.2.1

lemma fullEval_ptr_frame (n m : ℕ) (s : Store) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ 6 ∨ j = 17) : (fullEval n m s).ptrs j = s.ptrs j := by
  unfold fullEval
  by_cases h3 : j = 3
  · subst j
    change (ArrayEquality.equalityEval n (redirect (BoundaryProgram.fullEval n m s))).ptrs 24 = _
    rw [ArrayEquality.equality_ptr_frame n _ 24 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),redirect_ptr24]
    exact BoundaryProgram.fullEval_ptr_frame n m s 3 (by omega)
  · rw [restore_ptr_ne _ j h3,
      ArrayEquality.equality_ptr_frame n _ j (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega),redirect_ptr_ne _ j h3 (by omega)]
    exact BoundaryProgram.fullEval_ptr_frame n m s j (by omega)

lemma fullEval_boundary_bitmap {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hC : Bitmap s.imem (s.ptrs 3) C)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) (v : Fin n) :
    (fullEval n es.length s).imem (address (s.ptrs 4) v) =
      if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0 := by
  rw [fullEval_imem]
  exact BoundaryProgram.fullEval_boundary_bitmap G C es s hC he hsep hesep hsound hcomplete v

lemma fullEval_imem_frame {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (fullEval n es.length s).imem x = s.imem x := by
  rw [fullEval_imem]
  exact BoundaryProgram.fullEval_imem_frame es s he hesep x hx


/- Equality of exact zero/one bitmap cells is equality of the represented sets. -/
lemma bitmap_equal_iff {n : ℕ} (mem : ℤ → ℤ) (a b : ℤ)
    (S T : Finset (Fin n)) (hS : Bitmap mem a S) (hT : Bitmap mem b T) :
    (∀ v : Fin n, mem (address a v) = mem (address b v)) ↔ S = T := by
  constructor
  · intro h
    apply Finset.ext
    intro v
    have hv := h v
    rw [hS v,hT v] at hv
    by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;> simp_all
  · rintro rfl v
    rw [hS v,hT v]

lemma compare_inputs {n : ℕ} (G : SimpleGraph (Fin n))
    (C S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hC : Bitmap s.imem (s.ptrs 3) C) (hS : Bitmap s.imem (s.ptrs 17) S)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hSsep : Separate (n := n) (s.ptrs 17) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    let x := redirect (BoundaryProgram.fullEval n es.length s)
    Bitmap x.imem (x.ptrs 3) S ∧
    Bitmap x.imem (x.ptrs 4) (BoundaryMemory.externalBoundary G C) := by
  dsimp only
  constructor
  · rw [redirect_imem,redirect_ptr3,
      BoundaryProgram.fullEval_ptr_frame n es.length s 17 (by omega)]
    intro v
    rw [BoundaryProgram.fullEval_imem_frame es s he hesep _ (hSsep v)]
    exact hS v
  · rw [redirect_imem,redirect_ptr_ne _ 4 (by decide) (by decide),
      BoundaryProgram.fullEval_ptr_frame n es.length s 4 (by omega)]
    exact (BoundaryProgram.fullEval_boundary G C es s hC he hsep hesep hsound hcomplete).2

lemma fullEval_flag {n : ℕ} (G : SimpleGraph (Fin n))
    (C S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ))
    (hC : Bitmap s.imem (s.ptrs 3) C) (hS : Bitmap s.imem (s.ptrs 17) S)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hSsep : Separate (n := n) (s.ptrs 17) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    (fullEval n es.length s).ptrs 18 =
      if S = BoundaryMemory.externalBoundary G C then 1 else 0 := by
  let x := redirect (BoundaryProgram.fullEval n es.length s)
  have hn' : x.ptrs 6 = (n:ℤ) := by
    rw [redirect_ptr_ne _ 6 (by decide) (by decide),
      BoundaryProgram.fullEval_ptr_frame n es.length s 6 (by omega),hn]
  have hb := compare_inputs G C S es s hC hS he hsep hSsep hesep hsound hcomplete
  change (ArrayEquality.equalityEval n x).ptrs 18 = _
  rw [ArrayEquality.equality_flag n x hn']
  have heq := bitmap_equal_iff x.imem (x.ptrs 3) (x.ptrs 4) S
    (BoundaryMemory.externalBoundary G C) hb.1 hb.2
  by_cases h : S = BoundaryMemory.externalBoundary G C
  · have h' : ∀ i : Fin n, x.imem (x.ptrs 3 + (i.val:ℤ)) =
        x.imem (x.ptrs 4 + (i.val:ℤ)) := heq.mpr h
    simp [h,h']
  · have h' : ¬ ∀ i : Fin n, x.imem (x.ptrs 3 + (i.val:ℤ)) =
        x.imem (x.ptrs 4 + (i.val:ℤ)) := fun h' => h (heq.mp h')
    simp [h,h']

lemma fullEval_flag_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (C S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ))
    (hC : Bitmap s.imem (s.ptrs 3) C) (hS : Bitmap s.imem (s.ptrs 17) S)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hSsep : Separate (n := n) (s.ptrs 17) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    (fullEval n es.length s).ptrs 18 = 1 ↔ S = BoundaryMemory.externalBoundary G C := by
  rw [fullEval_flag G C S es s hn hC hS he hsep hSsep hesep hsound hcomplete]
  by_cases h : S = BoundaryMemory.externalBoundary G C <;> simp [h]

/- Construct the external boundary and compare it against an ordinary candidate
bitmap, with a canonical Boolean flag and no precomputed answer as advice. -/
end StableMSR.Recovery.Compiler.TightBoundaryProgram

open StableMSR.Recovery.Compiler.TightBoundaryProgram StableMSR.Recovery.ComponentMemory
theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 61 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (C S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) →
      Bitmap s.imem (s.ptrs 3) C → Bitmap s.imem (s.ptrs 17) S →
      EdgeEncoding s.imem (s.ptrs 2) es →
      Separate (n := n) (s.ptrs 3) (s.ptrs 4) →
      Separate (n := n) (s.ptrs 17) (s.ptrs 4) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let B := Finset.univ.filter (fun v : Fin n => v ∉ C ∧ ∃ u ∈ C, G.Adj u v)
      let result := (MinSumFPT.step P d ω)^[15*n+17*es.length+21] (s.state 0 work)
      result.halted = true ∧ result.work = work+(15*n+17*es.length+21) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧
      result.cfg.ptrs 18 = (if S = B then 1 else 0) ∧
      (result.cfg.ptrs 18 = 1 ↔ S = B) ∧
      (∀ v : Fin n, result.imem (address (s.ptrs 4) v) =
        if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, (2 ≤ j ∧ j ≤ 6 ∨ j = 17) → result.cfg.ptrs j = s.ptrs j) := by
  refine ⟨program,compile_deterministic fullCmd 0,program_length,?_⟩
  intro n d G C S es s hm hn hC hS he hsep hSsep hesep hsound hcomplete ω work
  dsimp only
  rw [full_machine_execution d n es.length s hm hn ω work]
  have hf := fullEval_frame n es.length s
  exact ⟨rfl,rfl,hf.2.2.1,hf.2.2.2.1,hf.2.1,hf.1,
    fullEval_flag G C S es s hn hC hS he hsep hSsep hesep hsound hcomplete,
    fullEval_flag_iff G C S es s hn hC hS he hsep hSsep hesep hsound hcomplete,
    fullEval_boundary_bitmap G C es s hC he hsep hesep hsound hcomplete,
    fullEval_imem_frame es s he hesep,
    fullEval_ptr_frame n es.length s⟩

