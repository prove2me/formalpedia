-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.add_eq_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:33.51401+00:00
-- url     : https://prove2.me/submissions/b81917d4-e6ad-4154-aca6-911dc3c8d1e5

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
theorem _root_.solution {x y : K} {A B : ℝ} (hx : v x = A) (hy : v y = B) (h : A < B) :
    v (x + y) = A := by
  have hd : v x ≠ v y := by rw [hx, hy]; exact fun e => h.ne (WithTop.coe_injective e)
  rw [v.map_add_of_distinct_val hd, hx, hy, ← WithTop.coe_min, min_eq_left h.le]
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
