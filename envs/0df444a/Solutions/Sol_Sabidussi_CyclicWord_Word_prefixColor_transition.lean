-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.prefixColor_transition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:03.952889+00:00
-- url     : https://prove2.me/submissions/3785e6a7-eb06-4be9-a803-37c77ca90c7e

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
    W.prefixColor y (W.prev i) + W.prefixColor y i = y i := by
  by_cases hi : i = 0
  · subst i
    have hprev : W.prev 0 = Fin.last W.n := by
      apply (finRotate (W.n + 1)).injective
      simp [prev, finRotate_last]
    change (∑ j ∈ Finset.Iic (W.prev 0), y j) +
        (∑ j ∈ Finset.Iic 0, y j) = y 0
    rw [hprev, show Fin.last W.n = (⊤ : W.Pos) from rfl, Finset.Iic_top]
    change (∑ j, y j) + (∑ j ∈ Finset.Iic 0, y j) = y 0
    rw [htotal, zero_add]
    rw [show (0 : W.Pos) = ⊥ from rfl, Finset.Iic_bot]
    simp
  · have hprev : W.prev i = i - 1 := by
      exact finRotate_symm_apply i
    rw [prefixColor, prefixColor, hprev,
      Fin.Iic_sub_one_eq_Iio (Fin.pos_iff_ne_zero.mpr hi), Finset.Iic_eq_cons_Iio]
    rw [Finset.sum_cons]
    calc
      (∑ j ∈ Finset.Iio i, y j) + (y i + ∑ j ∈ Finset.Iio i, y j) =
          ((∑ j ∈ Finset.Iio i, y j) + ∑ j ∈ Finset.Iio i, y j) + y i := by abel
      _ = y i := by rw [color_add_self, zero_add]
end Sabidussi.CyclicWord.Word
