-- Prove2me | solution 1 for ReciprocityTheory.PTheta.ofRealVec_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:01.373053+00:00
-- url     : https://prove2.me/submissions/02f71dd6-dfb7-4236-865e-e582aa41ded0

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl

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
open ReciprocityTheory ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta
theorem _root_.solution (a u : ι → ℝ) : ofRealVec (a + u) = ofRealVec a + ofRealVec u := by
  funext i
  simp [ofRealVec]
end ReciprocityTheory.PTheta
