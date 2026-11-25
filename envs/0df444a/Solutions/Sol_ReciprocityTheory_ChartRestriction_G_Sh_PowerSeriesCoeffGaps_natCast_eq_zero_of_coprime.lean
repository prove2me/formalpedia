-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_zero_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:00.85091+00:00
-- url     : https://prove2.me/submissions/0da06be4-f154-4a7d-97d0-d55629792ff3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_natCast_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_intCast_nonneg

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
theorem _root_.solution {p : ℕ} (hp1 : v (p : K) = 1) {c : ℕ}
    (hc : Nat.Coprime p c) : v (c : K) = 0 := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have hK : (a : K) * p + b * c = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have h0 := natCast_nonneg v c
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have h1 : 0 < v ((a : K) * p) := by
    rw [v.map_mul, hp1]
    calc (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
      _ = 0 + 1 := (zero_add 1).symm
      _ ≤ v (a : K) + 1 := add_le_add_left (intCast_nonneg v a) 1
  have h2 : 0 < v ((b : K) * c) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_left (intCast_nonneg v b))
  have h3 := v.map_add ((a : K) * p) ((b : K) * c)
  rw [hK, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
