-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Compiler.effects_newFrame
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:25:55.483871+00:00
-- url     : https://prove2.me/submissions/a5b01520-8db7-4d2e-8176-a7af362643ee

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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

private theorem private_541561795d_wd_add (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a + _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a + b) := (BitVec.ofInt_add a b).symm
end




section

private theorem private_8745cc2b10_wd_sub (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a - _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a - b) := by
  rw [sub_eq_add_neg a b, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
end










/-! ## Configurations and single steps -/





/-! ## Runs -/

























/-! ## Pieces of code -/















/-! ## Straight-line code -/







@[simp] theorem effects_nil (m : ℤ → BitVec W) : _root_.ThreeSumApsp.WordRam.effects [] m = m := rfl

@[simp] theorem effects_cons (i : _root_.EndStatement.Instr) (l : List _root_.EndStatement.Instr) (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects (i :: l) m = _root_.ThreeSumApsp.WordRam.effects l (_root_.ThreeSumApsp.WordRam.effect i m) := rfl

theorem effects_append (l₁ l₂ : List _root_.EndStatement.Instr) (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects (l₁ ++ l₂) m = _root_.ThreeSumApsp.WordRam.effects l₂ (_root_.ThreeSumApsp.WordRam.effects l₁ m) := by
  simp [_root_.ThreeSumApsp.WordRam.effects, List.foldl_append]







/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}



/-- The sum of two known numbers. -/
theorem effect_add (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.add i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a + b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_541561795d_wd_add]

/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.sub i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a - b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_8745cc2b10_wd_sub]





/-- Storing at the address a that the cell i holds. -/
theorem effect_store (j : ℤ) (hi : m i = _root_.ThreeSumApsp.WordRam.wd W a) (ha : _root_.ThreeSumApsp.WordRam.InRange W a) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.store i j) m = Function.update m a (m j) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hi, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd ha]









end known

/-! ## Branches and verdicts -/









/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}



theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m := Set.eqOn_refl m sᶜ

theorem AgreeOutside.trans (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₂) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₂ m₃) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁

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

/-- A statement may change the stack from its frame on. -/
theorem stack_subset_writable {q : ℕ} : _root_.Light.Compiler.Stack q Z.Q ⊆ _root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z q :=
  Set.subset_union_right.trans Set.subset_union_left





/-! ## Addresses, and numbers that fit in a word -/

/-- The cell of the local variable x of the frame q, computed from FP and the pool. -/
theorem cStack_sub (q x : ℕ) : _root_.Light.Compiler.cStack q - ((2 * x : ℕ) : ℤ) = _root_.Light.Compiler.cStack (q + x) := by
  simp only [_root_.Light.Compiler.cStack]
  push_cast
  ring

/-- Back from the frame q + x to the frame q. -/
theorem cStack_add (q x : ℕ) : _root_.Light.Compiler.cStack (q + x) + ((2 * x : ℕ) : ℤ) = _root_.Light.Compiler.cStack q := by
  simp only [_root_.Light.Compiler.cStack]
  push_cast
  ring

/-- The stack cell before the cell q + 1. -/
theorem cStack_succ_add (q : ℕ) : _root_.Light.Compiler.cStack (q + 1) + ((2 : ℕ) : ℤ) = _root_.Light.Compiler.cStack q := _root_.ThreeSum1960614.Machine.Light.Compiler.cStack_add q 1

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



/-- A memory that differs only in scratch cells and in the stack beyond the frame represents the
same state.  (Here and below 1 ≤ q is needed because stack cell 0 is memory cell 0.) -/
theorem Rel.beyond (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (hq : 1 ≤ q)
    (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch Z.F ∪ _root_.Light.Compiler.Stack (q + Z.F) Z.Q) m m') : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m' :=
  R.of_agreeOutside A (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) R.fp)
    (fun x hx => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R.loc x hx)) fun a ha => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R.mem a ha)









end Rel



/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List _root_.EndStatement.Instr}







end code

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Pieces of a call: the arguments and the new frame

A call first evaluates its arguments into T₀, T₁, … (`effects_argsCode`).  Then it sets up the frame
of the procedure, F + 1 stack cells further on (`effects_newFrame`): NFP receives the new frame
pointer, the local variables of the new frame receive the arguments and zeros
(`effects_frameInit`), the stack cell before the new frame receives the position to return to, and
FP moves to the new frame.  After that the memory represents the state in which the procedure
starts.
-/

public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q : ℕ} {m : ℤ → BitVec W}

/-! ## The arguments -/





/-! ## The new frame -/

section

/-- The code for one more local variable. -/
private theorem private_cef2144472_frameInit_succ (F' n : ℕ) : _root_.Light.Compiler.frameInit (F' + 1) n = _root_.Light.Compiler.frameInit F' n ++
    [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cNFP (_root_.Light.Compiler.cPool (2 * F')), _root_.EndStatement.Instr.store _root_.Light.Compiler.cADDR (if F' < n then _root_.Light.Compiler.cT F' else _root_.Light.Compiler.cZERO)] := by
  simp [_root_.Light.Compiler.frameInit, List.range_succ, List.flatMap_append]
end




section

/-- The code that fills the first F' local variables of the new frame at q': the first n from the
temporaries, the others with 0.  It changes nothing but ADDR and stack cells from q' on. -/
private theorem private_3cad52fdbb_effects_frameInit (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) (n q' F' : ℕ) (m : ℤ → BitVec W)
    (hNFP : m _root_.Light.Compiler.cNFP = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack q'))
    (hpool : ∀ i < F', m (_root_.Light.Compiler.cPool (2 * i)) = _root_.ThreeSumApsp.WordRam.wd W ((2 * i : ℕ) : ℤ)) (hQ : q' + F' ≤ Z.Q) :
    (∀ i < F',
        _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameInit F' n) m (_root_.Light.Compiler.cStack (q' + i)) = if i < n then m (_root_.Light.Compiler.cT i) else m _root_.Light.Compiler.cZERO) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (insert _root_.Light.Compiler.cADDR (_root_.Light.Compiler.Stack q' Z.Q)) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameInit F' n) m) := by
  induction F' with
  | zero => exact ⟨fun i h => absurd h (by omega), _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m⟩
  | succ F' ih =>
    obtain ⟨val, A⟩ := ih (fun i hi => hpool i (by omega)) (by omega)
    -- ADDR := NFP - 2 F'; the cell at ADDR := T_{F'} or 0
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_cef2144472_frameInit_succ, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cADDR (A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) hNFP) (A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (hpool F' (by omega))),
      _root_.ThreeSum1960614.Machine.Light.Compiler.cStack_sub, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨fun i hi => ?_, (A.update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _).update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _⟩
    obtain rfl | hne := eq_or_ne i F'
    · rw [Function.update_self]
      split_ifs <;> rw [Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), A.cell (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))]
    · have hstack : _root_.Light.Compiler.cStack (q'+i) ≠ _root_.Light.Compiler.cStack (q'+F') := by
        simp only [_root_.Light.Compiler.cStack]
        omega
      have haddr : _root_.Light.Compiler.cStack (q'+i) ≠ _root_.Light.Compiler.cADDR := by
        simp only [_root_.Light.Compiler.cStack,_root_.Light.Compiler.cADDR]
        omega
      rw [Function.update_of_ne hstack,Function.update_of_ne haddr]
      exact val i (by omega)
end






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

variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q : ℕ} {m : ℤ → BitVec W}
section

/-- The new frame.  If T₀, T₁, … hold the values of the arguments, then afterwards the memory
represents the state in which the procedure starts, in the frame q + F + 1, and the stack cell
before that frame holds the position to return to.  Of the stack, only cells from q + F on have
changed. -/
theorem ThreeSum1960614.Machine.Light.Compiler.effects_newFrame__implementation_9d32bedaad (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (hQ : q + Z.F + 1 + Z.F ≤ Z.Q) (args : List _root_.ThreeSum1960614.Machine.Light.Expr)
    (hargs : ∀ i < args.length, m (_root_.Light.Compiler.cT i) = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.frame (args.map (·.val σ)) i)) {ret : ℕ}
    (hret : ret ≤ Z.disp) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z ⟨_root_.Light.frame (args.map (·.val σ)), σ.mem⟩ (q + Z.F + 1)
        (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.newFrame Z.F args.length ret) m) ∧
      _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.newFrame Z.F args.length ret) m (_root_.Light.Compiler.cStack (q + Z.F)) = _root_.ThreeSumApsp.WordRam.wd W ret ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z (q + Z.F)) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.newFrame Z.F args.length ret) m) := by
  have R := I.rel
  have hq := I.low
  have hN := Z.offsets_le
  simp only [_root_.Light.Compiler.newFrame, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil]
  -- NFP := FP - 2 (F + 1).  Up to the last instruction, only scratch cells and the stack beyond the
  -- frame q change, so the memory goes on representing σ in the frame q.
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cNFP R.fp (R.pool _ hN), _root_.ThreeSum1960614.Machine.Light.Compiler.cStack_sub, ← Nat.add_assoc]
  have A₁ := (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl (_root_.Light.Compiler.Scratch Z.F ∪ _root_.Light.Compiler.Stack (q + Z.F) Z.Q) m).update (a := _root_.Light.Compiler.cNFP) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
    (_root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack (q + Z.F + 1)))
  -- the local variables of the new frame
  obtain ⟨val, A⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_3cad52fdbb_effects_frameInit Z args.length (q + Z.F + 1) Z.F _
    (Function.update_self _root_.Light.Compiler.cNFP _ m) (fun i hi => (R.beyond hq A₁).pool _ (by omega)) hQ
  generalize _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameInit Z.F args.length) _ = m₂ at val A ⊢
  have hNFP : m₂ _root_.Light.Compiler.cNFP = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack (q + Z.F + 1)) :=
    A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (Function.update_self _ _ _)
  have A₂ := A₁.trans (A.mono (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))))
  -- ADDR := NFP + 2
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add _root_.Light.Compiler.cADDR hNFP ((R.beyond hq A₂).pool 2 (by omega)), _root_.ThreeSum1960614.Machine.Light.Compiler.cStack_succ_add]
  have A₃ := A₂.update (a := _root_.Light.Compiler.cADDR) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (_root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack (q + Z.F)))
  -- the cell at ADDR := ret
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega)),
    (R.beyond hq A₃).pool ret hret]
  have A₄ := A₃.update (a := _root_.Light.Compiler.cStack (q + Z.F)) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (_root_.ThreeSumApsp.WordRam.wd W ret)
  have R₄ := R.beyond hq A₄
  -- FP := NFP + 0
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add _root_.Light.Compiler.cFP (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact hNFP))) R₄.zero, add_zero]
  refine ⟨?_, by (repeat
                    (first
                      | rw [_root_.Function.update_self]
                      | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))])),
    (A₄.mono (Set.union_subset _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable _root_.ThreeSum1960614.Machine.Light.Compiler.stack_subset_writable)).update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _⟩
  refine R₄.of_agreeOutside ((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl {_root_.Light.Compiler.cFP} _).update rfl _) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
    (Function.update_self _ _ _) (fun i hi => ?_)
    fun a ha => (Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _ _).trans (R₄.mem a ha)
  -- local variable i of the new frame: argument i, or 0
  (repeat
     (first
       | rw [_root_.Function.update_self]
       | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))
  rw [val i hi]
  split_ifs with h
  · ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact hargs i h))
  · (repeat
       (first
         | rw [_root_.Function.update_self]
         | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))
    rw [R.zero]
    simp [_root_.Light.frame, List.getElem?_eq_none (not_lt.1 h)]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Compiler.effects_newFrame__implementation_9d32bedaad) := (@ThreeSum1960614.Machine.Light.Compiler.effects_newFrame__implementation_9d32bedaad)

#print axioms solution
