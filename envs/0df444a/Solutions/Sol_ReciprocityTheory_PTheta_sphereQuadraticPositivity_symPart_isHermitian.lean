-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.symPart_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:47.883633+00:00
-- url     : https://prove2.me/submissions/458a4580-bfbe-472b-86f3-211b942ff730

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
theorem _root_.solution (A : Matrix ι ι ℝ) : (A + Aᵀ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp [add_comm]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
