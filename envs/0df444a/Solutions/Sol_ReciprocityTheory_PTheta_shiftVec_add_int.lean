-- Prove2me | solution 1 for ReciprocityTheory.PTheta.shiftVec_add_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:36.356471+00:00
-- url     : https://prove2.me/submissions/fdb37d6d-ef74-4b71-9418-d13ec82d5ac0

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
theorem _root_.solution (a : ι → ℝ) (l n : ι → ℤ) :
    shiftVec (a + fun i => (n i : ℝ)) l = shiftVec a (l + n) := by
  funext i
  simp only [shiftVec, Pi.add_apply, Int.cast_add, Complex.ofReal_add, Complex.ofReal_intCast]
  ring
end ReciprocityTheory.PTheta
