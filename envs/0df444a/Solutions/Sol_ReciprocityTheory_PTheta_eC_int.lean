-- Prove2me | solution 1 for ReciprocityTheory.PTheta.eC_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:59.448519+00:00
-- url     : https://prove2.me/submissions/b78d5b3c-0ba5-464e-ae86-d323e3de9125

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
namespace ReciprocityTheory.PTheta
theorem _root_.solution (k : ℤ) : eC (k : ℂ) = 1 := by
  unfold eC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k
end ReciprocityTheory.PTheta
