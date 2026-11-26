-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.quadratic_incident_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:31.103127+00:00
-- url     : https://prove2.me/submissions/5f6d2a5e-337d-4427-b39a-39ad3f650e2e

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_chosenDifference
import Theorems.Thm_Sabidussi_CyclicWord_Word_prefixColor_prev_eq_strictPrefix
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_orderedLetterInteraction
import Theorems.Thm_Sabidussi_CyclicWord_Word_chosen_localQuadratic
import Theorems.Thm_Sabidussi_CyclicWord_Word_chosen_externalInteraction_eq_zero
import Theorems.Thm_Sabidussi_CyclicWord_Word_quadratic_prefix_pair
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
    (choice : V → Fin 3)
    (hbalanced : ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0)
    (v : V) :
    let y := W.chosenDifference hmin choice
    let x := W.prefixColor y
    ∑ os : W.Occurrence v × Fin 2, quadratic (W.incidentColor x os.1 os.2) = 0 := by
  dsimp only
  let y := W.chosenDifference hmin choice
  let x := W.prefixColor y
  have htotal : ∑ i, y i = 0 := W.sum_chosenDifference hmin choice
  have hstrict :
      (∑ i : W.Occurrence v, bracket (y i.1) (x (W.prev i.1))) =
        ∑ i : W.Occurrence v, ∑ j ∈ Finset.Iio i.1, bracket (y i.1) (y j) := by
    apply Fintype.sum_congr
    intro i
    rw [show x (W.prev i.1) = ∑ j ∈ Finset.Iio i.1, y j from
      W.prefixColor_prev_eq_strictPrefix y htotal i.1]
    change bracketRightHom (y i.1) (∑ j ∈ Finset.Iio i.1, y j) = _
    exact map_sum (bracketRightHom (y i.1)) y (Finset.Iio i.1)
  have hsplit :
      (∑ u, W.orderedLetterInteraction y v u) =
        (∑ u ∈ Finset.univ.erase v, W.orderedLetterInteraction y v u) +
          W.orderedLetterInteraction y v v := by
    exact (Finset.sum_erase_add Finset.univ
      (fun u ↦ W.orderedLetterInteraction y v u) (Finset.mem_univ v)).symm
  calc
    (∑ os : W.Occurrence v × Fin 2, quadratic (W.incidentColor x os.1 os.2)) =
        ∑ i : W.Occurrence v,
          (quadratic (x (W.prev i.1)) + quadratic (x i.1)) := by
            rw [Fintype.sum_prod_type]
            apply Fintype.sum_congr
            intro i
            rw [Fin.sum_univ_two]
            rfl
    _ = ∑ i : W.Occurrence v,
          (quadratic (y i.1) + bracket (y i.1) (x (W.prev i.1))) := by
            apply Fintype.sum_congr
            intro i
            exact W.quadratic_prefix_pair y htotal i.1
    _ = (∑ i : W.Occurrence v, quadratic (y i.1)) +
          ∑ i : W.Occurrence v, bracket (y i.1) (x (W.prev i.1)) := by
            exact Finset.sum_add_distrib
    _ = (∑ i : W.Occurrence v, quadratic (y i.1)) +
          ∑ u, W.orderedLetterInteraction y v u := by
            rw [hstrict, W.sum_orderedLetterInteraction y v]
    _ = ((∑ i : W.Occurrence v, quadratic (y i.1)) +
          W.orderedLetterInteraction y v v) +
          ∑ u ∈ Finset.univ.erase v, W.orderedLetterInteraction y v u := by
            rw [hsplit]
            abel
    _ = 0 := by
      rw [show (∑ i : W.Occurrence v, quadratic (y i.1)) +
          W.orderedLetterInteraction y v v = 0 from
            W.chosen_localQuadratic hmin choice v]
      rw [show (∑ u ∈ Finset.univ.erase v, W.orderedLetterInteraction y v u) = 0 from
        W.chosen_externalInteraction_eq_zero hmin choice hbalanced v]
      simp
end Sabidussi.CyclicWord.Word
