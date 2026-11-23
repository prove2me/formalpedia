-- Prove2me | solution 1 for ReciprocityTheory.PTheta.ofRealVec_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:02.316708+00:00
-- url     : https://prove2.me/submissions/99b1ab5d-ed6b-4587-bc7a-923ccbe8a766

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
theorem _root_.solution (n : ι → ℤ) : ofRealVec (fun i => (n i : ℝ)) = ofIntVec n := by
  funext i
  simp [ofRealVec, ofIntVec]
end ReciprocityTheory.PTheta
