-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_pow_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:44.329861+00:00
-- url     : https://prove2.me/submissions/3eec8ba9-9aa7-4890-af9d-a6b12c30568c

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
variable {K : Type*} [Field K]
namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
theorem _root_.solution (f : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (a : K)
    (h0 : coeff 0 f = 0) (h1 : coeff 1 f = a) (hg : ∀ j, 2 ≤ j → j < M → coeff j f = 0)
    (n : ℕ) (hn : 2 ≤ n) : coeff M (f ^ n) = if n = M then a ^ M else 0 := by
  have hX : (X : PowerSeries K) ∣ f :=
    X_dvd_iff.mpr (by rw [← coeff_zero_eq_constantCoeff_apply]; exact h0)
  obtain ⟨g, rfl⟩ := hX
  have hg0 : coeff 0 g = a := by
    rw [← h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]
  have hd : (X : PowerSeries K) ^ (M - 1) ∣ g - C a := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_C]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [hg0]
    · rw [if_neg hm0.ne', sub_zero, ← coeff_succ_X_mul]
      exact hg (m + 1) (by omega) (by omega)
  have hdn : (X : PowerSeries K) ^ (M - 1) ∣ g ^ n - C a ^ n :=
    dvd_trans hd (sub_dvd_pow_sub_pow _ _ n)
  rw [mul_pow, coeff_X_pow_mul']
  by_cases hle : n ≤ M
  · rw [if_pos hle]
    by_cases heq : n = M
    · subst heq
      rw [if_pos rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow,
        ← coeff_zero_eq_constantCoeff_apply, hg0]
    · rw [if_neg heq]
      have h1' := (X_pow_dvd_iff.mp hdn) (M - n) (by omega)
      rw [map_sub, ← map_pow, coeff_C, if_neg (by omega), sub_zero] at h1'
      exact h1'
  · rw [if_neg hle, if_neg (by omega)]
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
