-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.shiftVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:11.731159+00:00
-- url     : https://prove2.me/submissions/9ceb97e3-d007-4cbd-b544-2bca8921f11c

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
theorem _root_.solution (a : ι → ℝ) (l : ι → ℤ) :
    shiftVec a l = ofRealVec (fun i => (l i : ℝ) + a i) := by
  funext i
  simp [shiftVec, ofRealVec]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
