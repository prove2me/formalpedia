-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.I2.sqrt_exp_neg_div_eight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:27:15.331859+00:00
-- url     : https://prove2.me/submissions/ba856905-6e5f-4b1d-aef5-019544cf1fb2

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x : ℝ) : Real.sqrt (Real.exp (-x / 8)) = Real.exp (-x / 16) := by
  rw [show -x / 8 = -x / 16 + -x / 16 by ring, Real.exp_add,
    Real.sqrt_mul_self (Real.exp_pos _).le]
end ReciprocityTheory.ChartRestriction.G.I2
