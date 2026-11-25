-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_pow_mul_mem_aa197e5832ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:50.60649+00:00
-- url     : https://prove2.me/submissions/20f165d3-5770-4204-8e57-dd0f84eb05ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_inv_367f1c26964d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_pow_d9d354672a82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_mem_chartRing_2e95e89691d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_mul_d91c22cfe178
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_zero_4d4e53901f14


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
    {z : (Σ k, ι k) → ℂ} (hzP : z ∈ mcPts (mCoordIdeal y)) (hyc : segreCoord y c ≠ 0)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {f r : Ω} (hf : IsUnitAt y f z) {n : ℕ}
    (hr : f ^ n * r ∈ chartRing ℤ (segreCoord y) c) : ∃ v, IsValueAt y r z v := by
  obtain ⟨w, hw⟩ := exists_isValueAt_of_mem_chartRing hyc hz hr
  obtain ⟨a, ha, ha0⟩ := hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact ha0 (isValueAt_zero hzP ha)
  have hinv := isValueAt_pow (isValueAt_inv ha hf0 ha0) n
  refine ⟨w * a⁻¹ ^ n, ?_⟩
  have := isValueAt_mul hw hinv
  rwa [mul_comm (f ^ n) r, mul_assoc, ← mul_pow, mul_inv_cancel₀ hf0, one_pow, mul_one] at this
end GroundTheory.Heights₂.Heights.LowerBoundFree
