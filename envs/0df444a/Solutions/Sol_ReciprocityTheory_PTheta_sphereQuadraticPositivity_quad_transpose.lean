-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:10.351791+00:00
-- url     : https://prove2.me/submissions/7e11893a-94ae-4394-90f4-ebbc8ad6f8ea

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
theorem _root_.solution (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, vecMul_transpose]
  exact dotProduct_comm _ _
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
