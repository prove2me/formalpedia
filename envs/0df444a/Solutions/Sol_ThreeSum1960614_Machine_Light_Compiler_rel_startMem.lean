-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Compiler.rel_startMem
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:21:11.521423+00:00
-- url     : https://prove2.me/submissions/569294f2-ddb7-464a-82c6-3e8eb4fdec45

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
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

/-- The only constant. -/
theorem effect_one (i : ℤ) : _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.one i) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W 1) := rfl

/-- The sum of two known numbers. -/
theorem effect_add (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.add i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a + b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_541561795d_wd_add]

/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.sub i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a - b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_8745cc2b10_wd_sub]















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

/-- A change inside s, then a change inside t. -/
theorem AgreeOutside.trans_union (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₂) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside t m₂ m₃) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (s ∪ t) m₁ m₃ :=
  (h₁.mono Set.subset_union_left).trans (h₂.mono Set.subset_union_right)

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



theorem WritesIn.mono {i : _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (hst : s ⊆ t) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn t i := by
  cases i <;> first | exact hst h | exact h

section

private theorem private_e74ef30073_agreeOutside_effect {i : _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (_root_.ThreeSumApsp.WordRam.effect i m) := by
  cases i <;>
    first | exact (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m).update h _ | exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m | exact h.elim
end


/-- Code without stores changes only the cells that its instructions name as their targets. -/
theorem agreeOutside_effects {l : List _root_.EndStatement.Instr} (h : ∀ i ∈ l, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (_root_.ThreeSumApsp.WordRam.effects l m) := by
  induction l generalizing m with
  | nil => exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 h
    exact (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_e74ef30073_agreeOutside_effect hi m).trans (ih hl _)

end framing

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The start-up code

A compiled program may start on any memory: nothing is assumed about the cells below -2.  Its first
three instructions and its start-up code write everything that the compiled statements rely on.
`startMem F N m` is the memory in which the outermost statement starts, if the run starts in m.

* `rel_startMem`: it represents the state in which the local variables 1 and 2 hold the two
  arguments (the contents of the cells -1 and -2) and all other local variables hold 0.
* `agreeOutside_startMem`: it differs from m only in the registers for 1, 0, -1, in the pool, in FP
  and in the outermost frame.
* `steps_start`: the machine gets from position 0 to the outermost statement in N + F + 9 steps.

The code has three pieces: the numbers 1, 0, -1 (`headStraight`), the pool (`poolCode`), the
outermost frame (`frameCode`).  There is no store among them, so the cells that a piece may change
are read off its text (`agreeOutside_effects`).  What a piece writes is found by running it: the two
loops unrolled in the code are inductions (`effects_poolCode`, `effects_zeroCode`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

/-! ## The numbers 1, 0, -1 -/

section

private theorem private_39e5ba589c_effects_headStraight (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m =
      Function.update (Function.update (Function.update m _root_.Light.Compiler.cONE (_root_.ThreeSumApsp.WordRam.wd W 1)) _root_.Light.Compiler.cZERO (_root_.ThreeSumApsp.WordRam.wd W 0)) _root_.Light.Compiler.cNEG
        (_root_.ThreeSumApsp.WordRam.wd W (-1)) := by
  simp only [_root_.Light.Compiler.headStraight, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil]
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_one, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cZERO (by (repeat
                                                                                                                                                                        (first
                                                                                                                                                                          | rw [_root_.Function.update_self]
                                                                                                                                                                          | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))) (by (repeat
                                                                                                                                                                                       (first
                                                                                                                                                                                         | rw [_root_.Function.update_self]
                                                                                                                                                                                         | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))),
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cNEG (by (repeat
                                                                                                     (first
                                                                                                       | rw [_root_.Function.update_self]
                                                                                                       | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))) (by (repeat
                                                                                                                    (first
                                                                                                                      | rw [_root_.Function.update_self]
                                                                                                                      | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))])))]
  rfl
end


section

/-- The three registers after the first three instructions. -/
private theorem private_022aab1f82_effects_headStraight_consts (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1 ∧ _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m _root_.Light.Compiler.cZERO = _root_.ThreeSumApsp.WordRam.wd W 0 ∧
      _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m _root_.Light.Compiler.cNEG = _root_.ThreeSumApsp.WordRam.wd W (-1) := by
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_39e5ba589c_effects_headStraight]
  refine ⟨?_, ?_, ?_⟩ <;> (repeat
                             (first
                               | rw [_root_.Function.update_self]
                               | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))
end


/-! ## The pool -/

section

private theorem private_8d16c9afc2_poolCode_succ (N : ℕ) :
    _root_.Light.Compiler.poolCode (N + 1) = _root_.Light.Compiler.poolCode N ++ [_root_.EndStatement.Instr.add (_root_.Light.Compiler.cPool (N + 1)) (_root_.Light.Compiler.cPool N) _root_.Light.Compiler.cONE] := by
  simp [_root_.Light.Compiler.poolCode, List.range_succ]
end


section

private theorem private_1689400533_agreeOutside_poolCode (N : ℕ) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Pool N) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.poolCode N) m) := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (l := _root_.Light.Compiler.poolCode N)
    (List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun n hn => ?_⟩) m
  · show _root_.Light.Compiler.cPool 0 ∈ _root_.Light.Compiler.Pool N
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
  · have := List.mem_range.1 hn
    show _root_.Light.Compiler.cPool (n + 1) ∈ _root_.Light.Compiler.Pool N
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end


section

/-- After `poolCode N` the pool holds the numbers 0, …, N. -/
private theorem private_af24c90ce0_effects_poolCode (hone : m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1) (N : ℕ) :
    ∀ n ≤ N, _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.poolCode N) m (_root_.Light.Compiler.cPool n) = _root_.ThreeSumApsp.WordRam.wd W n := by
  induction N with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp only [_root_.Light.Compiler.poolCode, List.range_zero, List.map_nil, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil]
    rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _ hone hone, Function.update_self]
    rfl
  | succ N ih =>
    intro n hn
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_8d16c9afc2_poolCode_succ, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add _ (ih N le_rfl) ((_root_.ThreeSum1960614.Machine.Light.Compiler.private_1689400533_agreeOutside_poolCode N m).read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) hone)]
    obtain rfl | hlt := hn.eq_or_lt
    · rw [Function.update_self]
      push_cast
      rfl
    · rw [Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), ih n (by omega)]
end


section

/-- The memory after the first three instructions and the code for the pool. -/
private def private_54239f6749_poolMem (N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.poolCode N) (_root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m)
end


section

private theorem private_ace6a9ccfe_agreeOutside_poolMem (N : ℕ) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Constants N) m (_root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m) := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.trans_union ?_ (_root_.ThreeSum1960614.Machine.Light.Compiler.private_1689400533_agreeOutside_poolCode N _)
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_39e5ba589c_effects_headStraight]
  exact (((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m).update (by simp) _).update (by simp) _).update (by simp) _
end


section

/-- The code for the pool leaves the numbers 1, 0, -1 in their registers. -/
private theorem private_e83a5c8f0a_poolMem_consts (N : ℕ) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1 ∧ _root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m _root_.Light.Compiler.cZERO = _root_.ThreeSumApsp.WordRam.wd W 0 ∧ _root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m _root_.Light.Compiler.cNEG = _root_.ThreeSumApsp.WordRam.wd W (-1) := by
  obtain ⟨one, zero, neg⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_022aab1f82_effects_headStraight_consts m
  have keep := _root_.ThreeSum1960614.Machine.Light.Compiler.private_1689400533_agreeOutside_poolCode N (_root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m)
  exact ⟨keep.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) one, keep.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) zero, keep.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) neg⟩
end


section

private theorem private_6571f9d7c2_poolMem_pool (m : ℤ → BitVec W) {n : ℕ} (hn : n ≤ N) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m (_root_.Light.Compiler.cPool n) = _root_.ThreeSumApsp.WordRam.wd W n :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.private_af24c90ce0_effects_poolCode (_root_.ThreeSum1960614.Machine.Light.Compiler.private_022aab1f82_effects_headStraight_consts m).1 N n hn
end


/-! ## The outermost frame -/

section

private theorem private_a1b1fa1e28_zeroCode_succ (F : ℕ) :
    _root_.Light.Compiler.zeroCode (F + 1) = _root_.Light.Compiler.zeroCode F ++ [_root_.EndStatement.Instr.sub (_root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + F)) _root_.Light.Compiler.cONE _root_.Light.Compiler.cONE] := by
  simp [_root_.Light.Compiler.zeroCode, List.range_succ]
end


section

/-- The instructions of `zeroCode` write into the outermost frame. -/
private theorem private_71d3c3537a_writesIn_zeroCode (F : ℕ) : ∀ i ∈ _root_.Light.Compiler.zeroCode F, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn (_root_.Light.Compiler.MainFrame F) i :=
  List.forall_mem_map.2 fun x hx => by
    have := List.mem_range.1 hx
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + x) ∈ _root_.Light.Compiler.MainFrame F
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end


section

/-- The local variables of the outermost frame hold zeros. -/
private theorem private_fc536cb879_effects_zeroCode (hone : m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1) (F : ℕ) :
    ∀ x < F, _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.zeroCode F) m (_root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + x)) = _root_.ThreeSumApsp.WordRam.wd W 0 := by
  induction F with
  | zero => exact fun x hx => absurd hx x.not_lt_zero
  | succ F ih =>
    intro x hx
    have hone' := (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (_root_.ThreeSum1960614.Machine.Light.Compiler.private_71d3c3537a_writesIn_zeroCode F) m).read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) hone
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_a1b1fa1e28_zeroCode_succ, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _ hone' hone']
    obtain rfl | hlt := (Nat.lt_succ_iff.1 hx).eq_or_lt
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), ih x hlt]
end


section

private theorem private_9d050fcb47_agreeOutside_frameCode (h3 : 3 ≤ F) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside ({_root_.Light.Compiler.cFP} ∪ _root_.Light.Compiler.MainFrame F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameCode F) m) := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (l := _root_.Light.Compiler.frameCode F) (List.forall_mem_cons.2 ⟨?_,
    List.forall_mem_append.2 ⟨fun i hi => ?_, List.forall_mem_cons.2 ⟨?_,
      List.forall_mem_singleton.2 ?_⟩⟩⟩) m
  · -- FP := 0 - 2 mainFrame
    exact Or.inl rfl
  · -- the zeros
    exact (_root_.ThreeSum1960614.Machine.Light.Compiler.private_71d3c3537a_writesIn_zeroCode F i hi).mono Set.subset_union_right
  · -- local variable 1 := the first argument
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + 1) ∈ _
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
  · -- local variable 2 := the second argument
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + 2) ∈ _
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end


section

/-- The code for the outermost frame: FP, then zeros, then the two arguments. -/
private theorem private_1198b4229d_effects_frameCode {i j : ℤ} (hzero : m _root_.Light.Compiler.cZERO = _root_.ThreeSumApsp.WordRam.wd W 0)
    (hpool : m (_root_.Light.Compiler.cPool (2 * _root_.Light.Compiler.mainFrame)) = _root_.ThreeSumApsp.WordRam.wd W (2 * _root_.Light.Compiler.mainFrame : ℕ)) (hi : m _root_.Light.Compiler.cARG1 = _root_.ThreeSumApsp.WordRam.wd W i)
    (hj : m _root_.Light.Compiler.cARG2 = _root_.ThreeSumApsp.WordRam.wd W j) (F : ℕ) :
    _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameCode F) m =
      Function.update (Function.update
        (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.zeroCode F) (Function.update m _root_.Light.Compiler.cFP (_root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack _root_.Light.Compiler.mainFrame))))
        (_root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + 1)) (_root_.ThreeSumApsp.WordRam.wd W i)) (_root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + 2)) (_root_.ThreeSumApsp.WordRam.wd W j) := by
  -- what the last two instructions read has not been written since the beginning
  have read (a : ℤ) (ha : a ∉ _root_.Light.Compiler.MainFrame F) (hfp : a ≠ _root_.Light.Compiler.cFP) :
      _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.zeroCode F) (Function.update m _root_.Light.Compiler.cFP (_root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack _root_.Light.Compiler.mainFrame))) a = m a :=
    ((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (_root_.ThreeSum1960614.Machine.Light.Compiler.private_71d3c3537a_writesIn_zeroCode F) _).cell ha).trans (Function.update_of_ne hfp _ _)
  have zero := (read _root_.Light.Compiler.cZERO (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans hzero
  have arg1 := (read _root_.Light.Compiler.cARG1 (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans hi
  have arg2 := (read _root_.Light.Compiler.cARG2 (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans hj
  simp only [_root_.Light.Compiler.frameCode, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil]
  -- FP := 0 - 2 mainFrame
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cFP hzero hpool, show (0 : ℤ) - (2 * _root_.Light.Compiler.mainFrame : ℕ) = _root_.Light.Compiler.cStack _root_.Light.Compiler.mainFrame from rfl]
  -- after the zeros: local variable 1 := the first argument + 0
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add _ arg1 zero, add_zero]
  -- local variable 2 := the second argument + 0
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add _ (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact arg2))) (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact zero))), add_zero]
end


/-! ## The memory in which the outermost statement starts -/



section

private theorem private_1410a86b87_startMem_eq (F N : ℕ) (m : ℤ → BitVec W) :
    _root_.Light.Compiler.startMem F N m = _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameCode F) (_root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m) := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append _ _ _
end






/-! ## The run from the first instruction to the outermost statement -/









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

variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}
section

/-- After the start-up code the memory represents the state in which the outermost statement
starts: the local variables 1 and 2 hold the two arguments, all others 0.  Nothing is assumed about
the cells below -2 of the initial memory. -/
theorem ThreeSum1960614.Machine.Light.Compiler.rel_startMem__implementation_8b5750d36e (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) (h3 : 3 ≤ Z.F) (hpool : 2 * _root_.Light.Compiler.mainFrame ≤ Z.disp) {μ : ℕ → ℤ}
    {i j : ℤ} (hm : ∀ a < Z.lim.space, m (a : ℤ) = _root_.ThreeSumApsp.WordRam.wd W (μ a)) (hi : m _root_.Light.Compiler.cARG1 = _root_.ThreeSumApsp.WordRam.wd W i)
    (hj : m _root_.Light.Compiler.cARG2 = _root_.ThreeSumApsp.WordRam.wd W j) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z ⟨_root_.Light.frame [0, i, j], μ⟩ _root_.Light.Compiler.mainFrame (_root_.Light.Compiler.startMem Z.F Z.disp m) := by
  obtain ⟨one, zero, neg⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_e83a5c8f0a_poolMem_consts Z.disp m
  have keep₁ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ace6a9ccfe_agreeOutside_poolMem Z.disp m
  have keep₂ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_9d050fcb47_agreeOutside_frameCode h3 (_root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem Z.disp m)
  have written := _root_.ThreeSum1960614.Machine.Light.Compiler.private_1198b4229d_effects_frameCode zero (_root_.ThreeSum1960614.Machine.Light.Compiler.private_6571f9d7c2_poolMem_pool m hpool) (keep₁.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) hi)
    (keep₁.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) hj) Z.F
  have zeros (x : ℕ) (hx : x < Z.F) (h1 : x ≠ 1) (h2 : x ≠ 2) :
      _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameCode Z.F) (_root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem Z.disp m) (_root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + x)) = _root_.ThreeSumApsp.WordRam.wd W 0 := by
    rw [written, Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))]
    exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_fc536cb879_effects_zeroCode (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact one))) Z.F x hx
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_1410a86b87_startMem_eq]
  exact {
    one := keep₂.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) one
    zero := keep₂.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) zero
    neg := keep₂.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) neg
    pool := fun n hn => keep₂.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (_root_.ThreeSum1960614.Machine.Light.Compiler.private_6571f9d7c2_poolMem_pool m hn)
    fp := by
      rw [written, Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))),
        (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (_root_.ThreeSum1960614.Machine.Light.Compiler.private_71d3c3537a_writesIn_zeroCode Z.F) _).cell (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), Function.update_self]
    loc := fun x hx => match x with
      | 0 => zeros 0 hx (by omega) (by omega)
      | 1 => by rw [written, Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))]; exact Function.update_self ..
      | 2 => by rw [written]; exact Function.update_self ..
      | x + 3 => zeros (x + 3) hx (by omega) (by omega)
    mem := fun a ha => keep₂.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (keep₁.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (hm a ha)) }
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Compiler.rel_startMem__implementation_8b5750d36e) := (@ThreeSum1960614.Machine.Light.Compiler.rel_startMem__implementation_8b5750d36e)

#print axioms solution
