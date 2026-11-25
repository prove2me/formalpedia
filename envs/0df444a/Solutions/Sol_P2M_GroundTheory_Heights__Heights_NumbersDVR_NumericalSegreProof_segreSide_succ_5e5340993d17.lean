-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_segreSide_succ_5e5340993d17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:05.377627+00:00
-- url     : https://prove2.me/submissions/358a3950-c942-4743-9749-21e748fb5375

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_sum_antidiagonalTuple_succ_0f3573b289c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_snoc_zero_45b941bb4a84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_update_last_29ae083c48eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_zero_3772ad1e4116

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (hi : 1 ≤ i) (x : Fin (i + 1) → K → ℤ) (m : ℕ)
    (Y : List (K → ℤ)) :
    segreSide F P x (m + 1) Y =
      segreSide F P (fun j => x (Fin.castSucc j)) m Y +
        segreSide F P x m (x (Fin.last i) :: Y) := by
  unfold segreSide
  simp only [Nat.add_sub_cancel]
  by_cases h : i ≤ m + 1
  · obtain ⟨c, hc⟩ : ∃ c, m + 1 = i + c := ⟨m + 1 - i, by omega⟩
    rw [if_pos h, if_pos (by omega), show m + 1 - i = c by omega, show m - (i - 1) = c by omega]
    rcases c with _ | c
    · rw [if_neg (by omega), add_zero, Finset.Nat.antidiagonalTuple_zero_right,
        Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton, Finset.sum_singleton,
        rootList_zero, rootList_zero]
    · rw [if_pos (by omega), show m - i = c by omega, sum_antidiagonalTuple_succ]
      congr 1
      · refine Finset.sum_congr rfl fun α _ => ?_
        rw [rootList_snoc_zero]
      · refine Finset.sum_congr rfl fun β _ => ?_
        rw [rootList_update_last, List.append_assoc, List.singleton_append]
  · rw [if_neg h, if_neg (by omega), if_neg (by omega), add_zero]
end GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
