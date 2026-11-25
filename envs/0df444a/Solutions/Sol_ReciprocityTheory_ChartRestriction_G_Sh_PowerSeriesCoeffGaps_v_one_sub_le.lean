-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.v_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:42.308924+00:00
-- url     : https://prove2.me/submissions/73af56b0-959f-4879-9dfc-ef92b0840a83

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
theorem _root_.solution {ζ μ : K} {k : ℕ} (hk : k ≠ 0) (hζ : ζ ^ k = 1) (i : ℕ)
    (hμ : μ = ζ ^ i) : v (1 - ζ) ≤ v (1 - μ) := by
  have hv0 : v ζ = 0 := v_eq_zero_of_pow_eq_one (v := v) hk hζ
  have e : 1 - μ = (1 - ζ) * ∑ j ∈ Finset.range i, ζ ^ j := by
    rw [hμ]; linear_combination (geom_sum_mul ζ i)
  rw [e, v.map_mul]
  refine le_add_of_nonneg_right (v.map_le_sum fun j _ => ?_)
  rw [v.map_pow, hv0, smul_zero]
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
