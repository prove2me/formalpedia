-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:36.228228+00:00
-- url     : https://prove2.me/submissions/f4ce5674-a683-4ca2-a1d3-9629c6b08bed

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_natCast_nonneg

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
theorem _root_.solution (n : ℤ) : 0 ≤ v (n : K) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using natCast_nonneg v m
  · simpa [v.map_neg] using natCast_nonneg v m
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
