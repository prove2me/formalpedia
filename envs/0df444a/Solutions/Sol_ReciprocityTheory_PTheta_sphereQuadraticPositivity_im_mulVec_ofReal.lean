-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_mulVec_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:42.060688+00:00
-- url     : https://prove2.me/submissions/4deea6aa-b9a7-45cb-9111-73b2dbdb13be

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
theorem _root_.solution (τ : Matrix ι ι ℂ) (v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec v) i).im) = τ.map Complex.im *ᵥ v := by
  funext i
  simp [mulVec, dotProduct, ofRealVec, Complex.im_sum]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
