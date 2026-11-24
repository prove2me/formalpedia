-- Prove2me | solution 1 for ReciprocityTheory.PTheta.eC_neg_half_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:47.978792+00:00
-- url     : https://prove2.me/submissions/3d5f723f-8ec3-401a-bd02-6bc89be172df

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
theorem _root_.solution (k : ℤ) : eC (-(k : ℂ) / 2) = (-1) ^ k := by
  unfold eC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (-(k : ℂ) / 2)) = (k : ℂ) * (-(Real.pi * Complex.I)) by ring,
    Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num
end ReciprocityTheory.PTheta
