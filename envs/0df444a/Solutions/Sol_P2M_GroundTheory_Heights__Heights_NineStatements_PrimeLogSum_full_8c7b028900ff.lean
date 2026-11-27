-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_full_8c7b028900ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:42.003899+00:00
-- url     : https://prove2.me/submissions/114d5899-e76f-4487-8414-3d8cba6676d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PPrimeLogSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_term_le_cb387f1df1fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_small_le_4c7e124151d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_large_le_8775b716dccb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open Finset
open GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
namespace GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
theorem _root_.solution : Statement := by
  refine ⟨20, fun B hB P hP hcard => ?_⟩
  rw [← sum_filter_add_sum_filter_not P (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 16 * Real.log B := by
    calc ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1)
        ≤ ∑ p ∈ P with p ≤ B, 2 * (Real.log p / p) := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter] at hp
          exact term_le (hP p hp.1).two_le
      _ = 2 * ∑ p ∈ P with p ≤ B, Real.log p / p := by rw [mul_sum]
      _ ≤ 2 * (8 * Real.log B) := by
          gcongr
          apply small_le hB
          intro p hp
          simp only [mem_filter] at hp
          exact ⟨hP p hp.1, hp.2⟩
      _ = 16 * Real.log B := by ring
  have hlarge : ∑ p ∈ P with ¬ p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by
    apply large_le hB
    · intro p hp
      simp only [mem_filter] at hp
      omega
    · exact (card_filter_le _ _).trans hcard
  linarith
end GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
