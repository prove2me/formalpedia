-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.nsmul_one_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:18.928631+00:00
-- url     : https://prove2.me/submissions/172be694-b09c-4492-9ee6-64f079c99020

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
open ReciprocityTheory.PGsh PowerSeries
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))
namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
theorem _root_.solution (n : ℕ) : n • (1 : WithTop ℝ) = ((n : ℝ) : WithTop ℝ) := by
  rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
