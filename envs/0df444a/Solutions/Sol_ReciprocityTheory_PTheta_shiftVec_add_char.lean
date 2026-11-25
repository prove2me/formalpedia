-- Prove2me | solution 1 for ReciprocityTheory.PTheta.shiftVec_add_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:34.015316+00:00
-- url     : https://prove2.me/submissions/80e1d095-1084-4032-bf47-c3892d78e7bd

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
theorem _root_.solution (a u : ι → ℝ) (l : ι → ℤ) :
    shiftVec (a + u) l = shiftVec a l + ofRealVec u := by
  funext i
  simp only [shiftVec, ofRealVec, Pi.add_apply, Complex.ofReal_add]
  ring
end ReciprocityTheory.PTheta
