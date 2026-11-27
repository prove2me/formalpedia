-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.eq_of_nonneg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:56.154279+00:00
-- url     : https://prove2.me/submissions/716ca06e-38f7-40bc-9f1e-e16f11cc6e4a

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
theorem _root_.solution {x y : K} {A B : ℝ} (hA : A < 0) (hx : v x = A) (hy : v y = B)
    (h : 0 ≤ v (x + y)) : A = B := by
  by_contra hne
  have hd : v x ≠ v y := by rw [hx, hy]; exact fun e => hne (WithTop.coe_injective e)
  rw [v.map_add_of_distinct_val hd, hx, hy, ← WithTop.coe_min] at h
  have h' : (0 : ℝ) ≤ min A B := by exact_mod_cast h
  exact absurd h' (not_le.mpr (lt_of_le_of_lt (min_le_left A B) hA))
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
