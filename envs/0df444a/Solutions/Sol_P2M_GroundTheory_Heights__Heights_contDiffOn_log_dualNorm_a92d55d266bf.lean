-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:27.109826+00:00
-- url     : https://prove2.me/submissions/96472a41-c264-4a51-8a1f-0a5839e656eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceExhaustion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass

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
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (h : HermNorm n) :
    ContDiffOn ℝ ∞ (fun x : Fin n → ℂ => Real.log (h.dualNorm x)) {0}ᶜ := by
  intro x hx
  have hM : (h.matᵀ)⁻¹ *ᵥ x ≠ 0 := by
    intro h0
    have : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
        Matrix.one_mulVec]
    exact hx (by rw [← this, h0, Matrix.mulVec_zero]; rfl)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hM
  have hpos : 0 < ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ x) i‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hQ : ContDiff ℝ ∞ fun y : Fin n → ℂ => ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 := by
    refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)
  exact ((hQ.contDiffAt.sqrt hpos.ne').log (Real.sqrt_pos.mpr hpos).ne').contDiffWithinAt
end GroundTheory.Heights₂.Heights
