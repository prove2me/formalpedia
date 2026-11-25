-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_ofReal_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:43.848144+00:00
-- url     : https://prove2.me/submissions/5313502d-501f-44bc-8b8e-5c784b2f4a60

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
theorem _root_.solution (v : ι → ℝ) (w : ι → ℂ) :
    (ofRealVec v ⬝ᵥ w).im = v ⬝ᵥ (fun i => (w i).im) := by
  simp [dotProduct, ofRealVec, Complex.im_sum]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
