-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.Hf_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:31.530887+00:00
-- url     : https://prove2.me/submissions/697ea5e1-6baf-4155-82b4-76c64ead5f6a

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
theorem _root_.solution {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) : Hf 0 v = 0 := by
  simp [Hf]
end ReciprocityTheory.ChartRestriction.G.I2.ChA
