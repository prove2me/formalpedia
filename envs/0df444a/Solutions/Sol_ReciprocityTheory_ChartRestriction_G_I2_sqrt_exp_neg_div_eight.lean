-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.sqrt_exp_neg_div_eight
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:11.926833+00:00
-- url     : https://prove2.me/submissions/54c0fd41-5da7-4b71-b097-9dae3f8b20af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
theorem _root_.solution (x : ℝ) : Real.sqrt (Real.exp (-x / 8)) = Real.exp (-x / 16) := by
  first
    | (rw [show -x / 8 = -x / 16 + -x / 16 by ring, Real.exp_add]
       exact Real.sqrt_mul_self (Real.exp_pos _).le)

