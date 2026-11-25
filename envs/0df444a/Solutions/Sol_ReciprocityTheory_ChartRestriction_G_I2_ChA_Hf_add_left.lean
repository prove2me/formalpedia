-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.Hf_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:26.503846+00:00
-- url     : https://prove2.me/submissions/5dcc260c-fe39-4823-bbd8-a09925b55a76

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
theorem _root_.solution {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.I2.ChA
