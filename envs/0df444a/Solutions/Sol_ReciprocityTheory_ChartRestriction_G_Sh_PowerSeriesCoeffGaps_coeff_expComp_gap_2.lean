-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_expComp_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:43.423046+00:00
-- url     : https://prove2.me/submissions/5d32435f-3eef-4346-aa57-75c9a335ebf0

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_coeff_pow_gap

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
variable {K : Type*} [Field K]
namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
theorem _root_.solution [CharZero K] (Ω : K) (lg : PowerSeries K) (M : ℕ) (hM : 2 ≤ M)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0) :
    coeff M (expComp Ω lg) = Ω * coeff M lg + Ω ^ M / (M.factorial : K) := by
  rw [expComp, coeff_mk, Finset.sum_range_succ, Finset.sum_eq_single 1]
  · rw [coeff_pow_gap lg M hM 1 hl0 hl1 hlg M hM, if_pos rfl]
    simp
  · intro d hd hd1
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      have hM0 : M ≠ 0 := by omega
      subst this; simp [coeff_one, hM0]
    · rw [coeff_pow_gap lg M hM 1 hl0 hl1 hlg d h,
        if_neg (by have := Finset.mem_range.mp hd; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
