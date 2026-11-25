-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_re_inner_negI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:11:56.428811+00:00
-- url     : https://prove2.me/submissions/7b66e5aa-1d47-4bd6-8e12-a5e9b98cd681

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [Fintype ι] (a x : EuclideanSpace ℂ ι) :
    inner ℝ a ((-Complex.I) • x) = (Hf x a).im := by
  simp only [real_inner_eq_re_inner ℂ, PiLp.inner_apply, Hf, Complex.re_sum, Complex.im_sum,
    PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, Complex.mul_im]
end ReciprocityTheory.ChartRestriction.G.I2
