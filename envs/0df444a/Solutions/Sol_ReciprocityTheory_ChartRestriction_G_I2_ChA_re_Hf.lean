-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.re_Hf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:17.975827+00:00
-- url     : https://prove2.me/submissions/81130957-727e-40d2-b7df-90f29ed979ba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA
namespace ReciprocityTheory.ChartRestriction.G.I2.ChA
theorem _root_.solution {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : (Hf v w).re = inner ℝ v w := by
  unfold Hf
  rw [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
end ReciprocityTheory.ChartRestriction.G.I2.ChA
