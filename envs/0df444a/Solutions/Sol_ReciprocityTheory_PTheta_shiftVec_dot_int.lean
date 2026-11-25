-- Prove2me | solution 1 for ReciprocityTheory.PTheta.shiftVec_dot_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:38.237774+00:00
-- url     : https://prove2.me/submissions/93f75c2b-c27b-42fe-822a-e74904662afa

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
    shiftVec a l ⬝ᵥ ofIntVec n = ((l ⬝ᵥ n : ℤ) : ℂ) + ofRealVec a ⬝ᵥ ofIntVec n := by
  simp only [dotProduct, shiftVec, ofIntVec, ofRealVec, add_mul, Finset.sum_add_distrib]
  push_cast
  rfl
end ReciprocityTheory.PTheta
