-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.sum_orderedLetterInteraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:31.585814+00:00
-- url     : https://prove2.me/submissions/dc5722e4-da0e-46cf-be66-27f1f9556e16

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
theorem _root_.solution (y : W.Pos → Color) (v : V) :
    (∑ u, W.orderedLetterInteraction y v u) =
      ∑ i : W.Occurrence v, ∑ j ∈ Finset.Iio i.1, bracket (y i.1) (y j) := by
  unfold orderedLetterInteraction
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i
  let e := Equiv.sigmaFiberEquiv W.letter
  calc
    (∑ u, ∑ j : W.Occurrence u,
        if j.1 < i.1 then bracket (y i.1) (y j.1) else 0) =
        ∑ p : Σ u, W.Occurrence u,
          if p.2.1 < i.1 then bracket (y i.1) (y p.2.1) else 0 := by
            symm
            exact Fintype.sum_sigma _
    _ = ∑ j : W.Pos, if j < i.1 then bracket (y i.1) (y j) else 0 := by
          apply Fintype.sum_equiv e
          rintro ⟨u, ⟨j, hj⟩⟩
          rfl
    _ = ∑ j ∈ Finset.Iio i.1, bracket (y i.1) (y j) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext j
            simp
          · intro j hj
            rfl
end Sabidussi.CyclicWord.Word
