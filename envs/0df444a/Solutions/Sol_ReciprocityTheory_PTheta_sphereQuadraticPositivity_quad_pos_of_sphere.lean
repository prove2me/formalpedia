-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_pos_of_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:54:24.925047+00:00
-- url     : https://prove2.me/submissions/1057906f-573d-4958-8e5b-48754c46078e

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_quad_smul
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_norm_inv_smul_mem_sphere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
theorem _root_.solution (A : Matrix ι ι ℝ)
    (h : ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < y ⬝ᵥ (A *ᵥ y)) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (A *ᵥ x) := by
  have h1 := h _ (norm_inv_smul_mem_sphere hx)
  rw [quad_smul] at h1
  have h2 : 0 ≤ ‖x‖⁻¹ ^ 2 := by positivity
  exact pos_of_mul_pos_right h1 h2
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
