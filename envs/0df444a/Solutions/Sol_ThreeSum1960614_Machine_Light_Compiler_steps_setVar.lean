-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Compiler.steps_setVar
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:14:59.186775+00:00
-- url     : https://prove2.me/submissions/b780b6eb-039d-427f-b771-b2b3fafbf328

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

variable {W : ℕ} {P : List _root_.EndStatement.Instr}

/-! ## Words -/





/-- The word of a number in the range of words, read as a signed number, is that number. -/
theorem toInt_wd {v : ℤ} (h : _root_.ThreeSumApsp.WordRam.InRange W v) : (_root_.ThreeSumApsp.WordRam.wd W v).toInt = v := by
  obtain ⟨hlo, hhi⟩ := h
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith







section

private theorem private_8745cc2b10_wd_sub (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a - _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a - b) := by
  rw [sub_eq_add_neg a b, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
end


section

private theorem private_6b248825b2_wd_one : (1 : BitVec W) = _root_.ThreeSumApsp.WordRam.wd W 1 := BitVec.eq_of_toNat_eq rfl
end








/-! ## Configurations and single steps -/





/-! ## Runs -/





section


private theorem Steps.private_ba3d5eb361_one {c c' : _root_.ThreeSumApsp.WordRam.Cfg W} (h : _root_.ThreeSumApsp.WordRam.step P c = .inl c') : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 c c' := ⟨c', h, rfl⟩
end


/-- One run after the other. -/
theorem Steps.trans {n k : ℕ} {c c₁ c₂ : _root_.ThreeSumApsp.WordRam.Cfg W} (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c c₁) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P k c₁ c₂) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P (n + k) c c₂ := by
  induction n generalizing c with
  | zero => obtain rfl := h₁; simpa using h₂
  | succ n ih =>
    obtain ⟨c', hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨c', hs, ih hr⟩

















/-! ## Pieces of code -/







/-- The second part of a piece of code follows the first. -/
theorem CodeAt.right {pos : ℕ} {l₁ l₂ : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (l₁ ++ l₂)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P (pos + l₁.length) l₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.drop_drop, ← hr, List.append_assoc, List.drop_left]

/-- The first instruction of a piece of code is the one that the machine finds at its position. -/
theorem CodeAt.head {pos : ℕ} {i : _root_.EndStatement.Instr} {l : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (i :: l)) :
    P.getD pos _root_.EndStatement.Instr.reject = i := by
  obtain ⟨r, hr⟩ := h
  have : (P.drop pos)[0]? = some i := by rw [← hr]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at this
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- A piece of code without its first instruction. -/
theorem CodeAt.tail {pos : ℕ} {i : _root_.EndStatement.Instr} {l : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (i :: l)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P (pos + 1) l :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt.right (l₁ := [i]) h



/-! ## Straight-line code -/













section

private theorem private_1baa6e787a_step_straight {c : _root_.ThreeSumApsp.WordRam.Cfg W} {i : _root_.EndStatement.Instr} (h : P.getD c.pc _root_.EndStatement.Instr.reject = i)
    (hi : _root_.ThreeSumApsp.WordRam.Straight i) : _root_.ThreeSumApsp.WordRam.step P c = .inl ⟨c.pc + 1, _root_.ThreeSumApsp.WordRam.effect i c.mem⟩ := by
  have write (a : ℤ) (v : BitVec W) :
      (fun x => if x = a then v else c.mem x) = Function.update c.mem a v := by
    funext x
    simp [Function.update_apply]
  cases i <;> simp only [_root_.ThreeSumApsp.WordRam.Straight] at hi <;> simp only [_root_.ThreeSumApsp.WordRam.step, h, _root_.ThreeSumApsp.WordRam.effect, write, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_6b248825b2_wd_one]
end


section

/-- One instruction that only changes the memory. -/
private theorem private_264a1a74c7_steps_instr {rest : List _root_.EndStatement.Instr} {pos : ℕ} {i : _root_.EndStatement.Instr}
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (i :: rest)) (hi : _root_.ThreeSumApsp.WordRam.Straight i) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨pos + 1, _root_.ThreeSumApsp.WordRam.effect i m⟩ :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps.private_ba3d5eb361_one (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_1baa6e787a_step_straight hcode.head hi)
end




/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}





/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.sub i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a - b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_8745cc2b10_wd_sub]





/-- Storing at the address a that the cell i holds. -/
theorem effect_store (j : ℤ) (hi : m i = _root_.ThreeSumApsp.WordRam.wd W a) (ha : _root_.ThreeSumApsp.WordRam.InRange W a) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.store i j) m = Function.update m a (m j) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hi, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd ha]



theorem steps_sub {rest : List _root_.EndStatement.Instr} {pos : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (_root_.EndStatement.Instr.sub i j k :: rest))
    (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a - b))⟩ :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub i hj hk ▸ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_264a1a74c7_steps_instr hcode trivial m



theorem steps_store {rest : List _root_.EndStatement.Instr} {pos : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (_root_.EndStatement.Instr.store i j :: rest))
    (hi : m i = _root_.ThreeSumApsp.WordRam.wd W a) (ha : _root_.ThreeSumApsp.WordRam.InRange W a) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m a (m j)⟩ :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_store j hi ha ▸ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_264a1a74c7_steps_instr hcode trivial m

end known

/-! ## Branches and verdicts -/









/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}



theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m := Set.eqOn_refl m sᶜ



theorem AgreeOutside.mono (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (hst : s ⊆ t) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside t m m' :=
  Set.EqOn.mono (Set.compl_subset_compl.2 hst) h



/-- A cell outside s is unchanged. -/
theorem AgreeOutside.cell (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := h ha

/-- A cell outside s still holds v. -/
theorem AgreeOutside.read (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∉ s) {v : BitVec W} (hv : m a = v) :
    m' a = v :=
  (h ha).trans hv

/-- Writing a cell of s. -/
theorem AgreeOutside.update (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∈ s) (v : BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (Function.update m' a v) :=
  fun x hx => (Function.update_of_ne (fun e : x = a => hx (e ▸ ha)) _ _).trans (h hx)









end framing

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The cells of the compiled code, and the memories that represent a state

The memory of the machine is one array indexed by the integers, and the compiled code keeps its
registers, temporaries, pool, stack and the memory of the light language in different parts of it.
Every proof about compiled code has to know that a write to one cell leaves the others alone.  This
file settles that once.

* Sets of cells: `Temps k F` (what evaluating an expression into T_k may change), `Scratch F` (what
  any compiled code uses freely), `Constants N` (what no compiled statement changes), `Writable Z q`
  (what a statement that runs in the frame q may change), and two parts of the memory, `Stack q Q`
  and `Pool N`.  "The memories m and m' differ only inside s" is `AgreeOutside s m m'`.
* The tactic `cells` proves that two cells are different, that a cell is or is not in one of these
  sets, or that one of these sets lies in another.  The tactic `cell_read` reads a cell of a memory
  that is given by writes.
* `Sizes W` collects the numbers that never change, with the assumptions on them: the layout of the
  code, the limits, the number of stack cells, and a word size W that fits them (`Fits`).
* `Rel Z σ q m`: the memory m represents the state σ in the frame q.  The relation survives changes
  of scratch cells (`Rel.same`) and of the stack beyond the frame (`Rel.beyond`); a write to the
  cell of a local variable or to a memory cell is the same write in the state (`Rel.setLoc`,
  `Rel.setMem`).  All four come from `Rel.of_agreeOutside`.  `Framed` adds that the frame lies
  within the stack.
* Two pieces of code that occur everywhere: the jump (`steps_jump`) and the two instructions that
  store a cell in a local variable (`steps_setVar`).

**Letters**, in this file and in the files on expressions, tests, calls and the simulation.
Numbers: W is the word size, F the number of local variables of a frame, N the largest number in the
pool, Q the number of stack cells, q a frame, pos a position in the code.  The temporaries are
written T₀, T₁, …, T_j; there are 2 F + 1 of them.
Facts: m, m₁, m₂, … are memories in the order in which they arise.  Z is a `Sizes`.  R says that a
memory represents a state (`Rel`), I the same with the frame inside the stack (`Framed`).  A says
that two memories agree outside a set of cells (`AgreeOutside`); A₂ speaks of m₂.  run is a run of
the machine (`Steps`).  val, va, vb say which number a cell holds.  hcode and names that end in Code
say where a piece of code is (`CodeAt`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## The numbers that never change -/







/-! ## Sets of cells -/















/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/













variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {F : ℕ}



/-- A statement may change scratch cells. -/
theorem scratch_subset_writable {q : ℕ} : _root_.Light.Compiler.Scratch Z.F ⊆ _root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z q :=
  (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left







/-! ## Addresses, and numbers that fit in a word -/

/-- The cell of the local variable x of the frame q, computed from FP and the pool. -/
theorem cStack_sub (q x : ℕ) : _root_.Light.Compiler.cStack q - ((2 * x : ℕ) : ℤ) = _root_.Light.Compiler.cStack (q + x) := by
  simp only [_root_.Light.Compiler.cStack]
  push_cast
  ring





/-- The addresses of the stack fit in a word. -/
theorem Sizes.inRange_stack (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : _root_.ThreeSumApsp.WordRam.InRange W (_root_.Light.Compiler.cStack j) := by
  have hjQ : (j : ℤ) ≤ Z.Q := by exact_mod_cast hj
  constructor <;> simp only [_root_.Light.Compiler.cStack] <;> linarith [Z.fits.stack]





/-! ## The relation between a state of the light language and a memory of the machine -/



section Rel

variable {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {q q' : ℕ} {m m' : ℤ → BitVec W}

/-- After a change that spares the numbers 1, 0, -1 and the pool, the new memory represents a state
as soon as FP, the local variables and the memory cells are right. -/
theorem Rel.of_agreeOutside {s : Set ℤ} (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m')
    (hs : s ⊆ (_root_.Light.Compiler.Constants Z.disp)ᶜ) (hfp : m' _root_.Light.Compiler.cFP = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack q'))
    (hloc : ∀ x < Z.F, m' (_root_.Light.Compiler.cStack (q' + x)) = _root_.ThreeSumApsp.WordRam.wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = _root_.ThreeSumApsp.WordRam.wd W (σ'.mem a)) : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ' q' m' := by
  have keep {a : ℤ} (ha : a ∈ _root_.Light.Compiler.Constants Z.disp) : m' a = m a := A.cell fun h => hs h ha
  exact {
    one := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.one
    zero := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.zero
    neg := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.neg
    pool := fun n hn => (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans (R.pool n hn)
    fp := hfp
    loc := hloc
    mem := hmem }

/-- A memory that differs only in scratch cells represents the same state. -/
theorem Rel.same (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch Z.F) m m') : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m' :=
  R.of_agreeOutside A (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) R.fp)
    (fun x hx => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R.loc x hx)) fun a ha => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R.mem a ha)



section


/-- Writing a local variable. -/
private theorem Rel.private_99343d306b_setLoc (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (hq : 1 ≤ q) (x : ℕ) (v : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z { σ with loc := Function.update σ.loc x v } q
      (Function.update m (_root_.Light.Compiler.cStack (q + x)) (_root_.ThreeSumApsp.WordRam.wd W v)) := by
  refine R.of_agreeOutside ((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl {_root_.Light.Compiler.cStack (q + x)} m).update rfl _) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
    (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact R.fp))) (fun y hy => ?_) fun a ha => by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact R.mem a ha))
  obtain rfl | hxy := eq_or_ne y x
  · simp
  · rw [Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))]
    exact (R.loc y hy).trans (by simp [hxy])
end








end Rel



/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List _root_.EndStatement.Instr}







end code

end Light.Compiler

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler

open _root_.EndStatement renaming Instr -> Instr
variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {F : ℕ}
open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler

variable {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List _root_.EndStatement.Instr}
section

/-- The two instructions that put the content v of the cell c into the local variable x. -/
theorem ThreeSum1960614.Machine.Light.Compiler.steps_setVar__implementation_892ddb9dff {x : ℕ} {c v : ℤ} (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (hx : x < Z.F)
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cFP (_root_.Light.Compiler.cPool (2 * x)) :: _root_.EndStatement.Instr.store _root_.Light.Compiler.cADDR c :: rest))
    (hc : m c = _root_.ThreeSumApsp.WordRam.wd W v) (hne : c ≠ _root_.Light.Compiler.cADDR) :
    ∃ m', _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code 2 ⟨pos, m⟩ ⟨pos + 2, m'⟩ ∧
      _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z { σ with loc := Function.update σ.loc x v } q m' ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z q) m m' := by
  have hN := Z.offsets_le
  have hQ := I.high
  -- ADDR := FP - 2 x
  have run₁ := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_sub (i := _root_.Light.Compiler.cADDR) hcode I.rel.fp (I.rel.pool (2 * x) (by omega))
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.cStack_sub] at run₁
  have A₁ := (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl (_root_.Light.Compiler.Scratch Z.F) m).update (a := _root_.Light.Compiler.cADDR) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
    (_root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack (q + x)))
  -- the cell at ADDR := c
  have run₂ := run₁.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_store hcode.tail (Function.update_self _ _ _)
    (Z.inRange_stack (by omega)))
  rw [Function.update_of_ne hne, hc] at run₂
  exact ⟨_, run₂, (I.rel.same A₁).private_99343d306b_setLoc I.low x v,
    (A₁.mono _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable).update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Compiler.steps_setVar__implementation_892ddb9dff) := (@ThreeSum1960614.Machine.Light.Compiler.steps_setVar__implementation_892ddb9dff)

#print axioms solution
