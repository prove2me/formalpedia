-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.norm_inv_smul_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:48.946585+00:00
-- url     : https://prove2.me/submissions/a2920970-d017-417b-afe3-e7275f878c09

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere

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
theorem _root_.solution {x : ι → ℝ} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
