-- Prove2me | solution 1 for ReciprocityTheory.PTheta.eC_eq_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:49.664853+00:00
-- url     : https://prove2.me/submissions/5f864a53-19f7-4a17-a5be-38777c23d499

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
theorem _root_.solution (x y : ℂ) (k : ℤ) (h : x = y + k) : eC x = eC y := by
  rw [h]
  simp only [eC]
  rw [mul_add, Complex.exp_add]
  have hk : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [hk, mul_one]
end ReciprocityTheory.PTheta
