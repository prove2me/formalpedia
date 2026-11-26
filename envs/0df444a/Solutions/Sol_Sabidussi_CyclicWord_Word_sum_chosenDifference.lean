-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.sum_chosenDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:13.322678+00:00
-- url     : https://prove2.me/submissions/e625950d-00e4-4669-aee4-2fee37cecdda

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_chosenDifference_occurrences
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
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) :
    ∑ i, W.chosenDifference hmin choice i = 0 := by
  let e := Equiv.sigmaFiberEquiv W.letter
  calc
    (∑ i, W.chosenDifference hmin choice i) =
        ∑ p : Σ v, W.Occurrence v, W.chosenDifference hmin choice p.2.1 := by
          symm
          simpa [e] using e.sum_comp (W.chosenDifference hmin choice)
    _ = ∑ v, ∑ o : W.Occurrence v, W.chosenDifference hmin choice o.1 := by
          exact Fintype.sum_sigma _
    _ = 0 := by
          apply Fintype.sum_eq_zero
          exact W.sum_chosenDifference_occurrences hmin choice
end Sabidussi.CyclicWord.Word
