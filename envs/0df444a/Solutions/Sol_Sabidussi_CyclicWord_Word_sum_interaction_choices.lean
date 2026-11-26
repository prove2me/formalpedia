-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.sum_interaction_choices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:11.288397+00:00
-- url     : https://prove2.me/submissions/f7adf1d6-b31f-416a-8513-45adfa715cff

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_frameDifference_choices
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_localDifference_one
import Theorems.Thm_Sabidussi_localDifference_zero
import Theorems.Thm_Sabidussi_sum_bracket_right
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
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v u : V) (cv : Fin 3) :
    ∑ cu, W.interaction hmin v u cv cu = 0 := by
  by_cases hvu : v = u
  · subst u
    simp [interaction]
  · simp only [interaction, if_neg hvu]
    rw [Finset.sum_comm]
    apply Fintype.sum_eq_zero
    intro i
    rw [Finset.sum_comm]
    apply Fintype.sum_eq_zero
    intro j
    by_cases hji : j.1 < i.1
    · simp only [hji, if_pos]
      calc
        (∑ cu, bracket (W.frameDifference hmin v cv i)
            (W.frameDifference hmin u cu j)) =
            bracket (W.frameDifference hmin v cv i)
              (∑ cu, W.frameDifference hmin u cu j) := sum_bracket_right _ _
        _ = 0 := by rw [W.sum_frameDifference_choices hmin u j]; simp
    · simp [hji]
end Sabidussi.CyclicWord.Word
