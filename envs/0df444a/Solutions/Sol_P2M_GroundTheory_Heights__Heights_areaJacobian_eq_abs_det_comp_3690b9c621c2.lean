-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_areaJacobian_eq_abs_det_comp_3690b9c621c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:58.428296+00:00
-- url     : https://prove2.me/submissions/89d0aba7-8354-439c-8f22-89c5b71d7bf2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaMultiplicity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Set Filter Function
open scoped ENNReal NNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : F ≃ₗᵢ[ℝ] E) (L : E →ₗ[ℝ] F) :
    areaJacobian L = |LinearMap.det (φ.toLinearIsometry.toLinearMap ∘ₗ L)| := by
  have h1 : areaJacobian L = L.normDet := by
    have h := L.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [areaJacobian, ← h, Real.sqrt_sq L.normDet_nonneg]
  rw [h1, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_comp_of_finrank_eq _ _ φ.toLinearEquiv.finrank_eq.symm,
    φ.toLinearIsometry.normDet_eq_one, one_mul]
end GroundTheory.Heights₂.Heights
