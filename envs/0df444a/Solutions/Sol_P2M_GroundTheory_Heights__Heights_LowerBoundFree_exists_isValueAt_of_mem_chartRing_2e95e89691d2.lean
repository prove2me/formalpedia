-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_mem_chartRing_2e95e89691d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:46.074402+00:00
-- url     : https://prove2.me/submissions/ccdf9579-8914-4433-90ae-efaf7d13a628

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_add_2f0a77fa72a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_intCast_7d5de349ae80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_prod_X_3f51a0201239
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_mul_d91c22cfe178


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hyc : segreCoord y c ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRing ℤ (segreCoord y) c) : ∃ v, IsValueAt y r z v := by
  classical
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    refine ⟨(∏ k, z ⟨k, c' k⟩) / ∏ k, z ⟨k, c k⟩, fun _ => 1, ∏ k, X ⟨k, c' k⟩, ∏ k, X ⟨k, c k⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isMultiHomog_prod_X c'
    · exact isMultiHomog_prod_X c
    · simpa [segreCoord] using hyc
    · simp only [map_prod, aeval_X]
      exact (div_mul_cancel₀ _ hyc).symm
    · simp only [map_prod, map_X, eval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hz k
    · simp [map_prod]
  | algebraMap n => exact ⟨n, by simpa using isValueAt_intCast y z n⟩
  | add a b _ _ ha hb =>
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨v + w, isValueAt_add hv hw⟩
  | mul a b _ _ ha hb =>
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨v * w, isValueAt_mul hv hw⟩
end GroundTheory.Heights₂.Heights.LowerBoundFree
