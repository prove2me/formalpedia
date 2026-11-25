-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.gN_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:12.654479+00:00
-- url     : https://prove2.me/submissions/e3721308-733f-4a0a-b86b-79568491bd6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (N : ℕ) : gN N 0 = 0 := by
  simp [gN, expN, Finset.sum_range_succ']
end ReciprocityTheory.ChartRestriction.G.I2.FPw
