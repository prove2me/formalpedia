-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.sum_frameDifference_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:00.126803+00:00
-- url     : https://prove2.me/submissions/004e496f-da0f-4ecd-8310-9c8a2eed3056

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
import Theorems.Thm_Sabidussi_sum_localDifference_occurrences
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
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) (v : V) (c : Fin 3) :
    ∑ o, W.frameDifference hmin v c o = 0 := by
  rw [← (W.occurrenceOrderIsoFin hmin v).symm.toEquiv.sum_comp]
  simpa [frameDifference] using sum_localDifference_occurrences
    (Fintype.card (W.Occurrence v) - 2) c
end Sabidussi.CyclicWord.Word
