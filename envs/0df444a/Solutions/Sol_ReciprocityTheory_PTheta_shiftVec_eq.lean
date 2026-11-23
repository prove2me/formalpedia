-- Prove2me | solution 1 for ReciprocityTheory.PTheta.shiftVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:02.730813+00:00
-- url     : https://prove2.me/submissions/9ed6050c-9a56-42aa-a804-44e89be9085e

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change

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
theorem _root_.solution (a : ι → ℝ) (l : ι → ℤ) : shiftVec a l = ofIntVec l + ofRealVec a := by
  rfl
end ReciprocityTheory.PTheta
