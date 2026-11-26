-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.prefixColor_prev_eq_strictPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:32.178107+00:00
-- url     : https://prove2.me/submissions/586c2f9b-25cd-49ed-a243-b2fccae9da38

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_localDifference_one
import Theorems.Thm_Sabidussi_localDifference_zero
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.localDifference_one
attribute [local simp] Sabidussi.localDifference_zero
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero



set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
open Sabidussi.CyclicWord.Word
variable (W : Word (V := V))
namespace Sabidussi.CyclicWord.Word
theorem _root_.solution
    (y : W.Pos → Color) (htotal : ∑ i, y i = 0) (i : W.Pos) :
    W.prefixColor y (W.prev i) = ∑ j ∈ Finset.Iio i, y j := by
  by_cases hi : i = 0
  · subst i
    have hprev : W.prev 0 = Fin.last W.n := by
      apply (finRotate (W.n + 1)).injective
      simp [prev]
    rw [prefixColor, hprev, show Fin.last W.n = (⊤ : W.Pos) from rfl, Finset.Iic_top]
    change (∑ j, y j) = ∑ j ∈ Finset.Iio 0, y j
    rw [htotal]
    rw [show (0 : W.Pos) = ⊥ from rfl, Finset.Iio_bot]
    simp
  · have hprev : W.prev i = i - 1 := finRotate_symm_apply i
    rw [prefixColor, hprev, Fin.Iic_sub_one_eq_Iio (Fin.pos_iff_ne_zero.mpr hi)]
end Sabidussi.CyclicWord.Word
