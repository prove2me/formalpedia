-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_eq_zero_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:38.775809+00:00
-- url     : https://prove2.me/submissions/5a405867-6f4e-4c57-90b1-eebd539772e3

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
theorem _root_.solution [IsAlgClosed K] [CharZero K] (lg : PowerSeries K) (M : ℕ)
    (hM : 2 ≤ M) (h : ∀ z : K, z ^ (M - 1) = 1 → rescale z lg = z • lg) (j : ℕ)
    (hj2 : 2 ≤ j) (hj : j < M) : coeff j lg = 0 := by
  have hN : M - 1 ≠ 0 := by omega
  have : NeZero ((M - 1 : ℕ) : K) := ⟨Nat.cast_ne_zero.mpr hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (M - 1) K)
    (Polynomial.degree_cyclotomic_pos (M - 1) K (Nat.pos_of_ne_zero hN)).ne'
  have hzp : IsPrimitiveRoot z (M - 1) := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hc := congrArg (coeff j) (h z hzp.pow_eq_one)
  rw [coeff_rescale, coeff_smul, smul_eq_mul] at hc
  by_contra hne
  have hz0 : z ≠ 0 := hzp.ne_zero hN
  have h1 : z ^ (j - 1) = 1 := by
    have h2 : z ^ j = z := mul_right_cancel₀ hne hc
    have hj' : j = (j - 1) + 1 := by omega
    rw [hj', pow_succ] at h2
    have h3 : z ^ (j - 1) * z = 1 * z := by rw [one_mul]; exact h2
    exact mul_right_cancel₀ hz0 h3
  have := Nat.le_of_dvd (by omega) (hzp.dvd_of_pow_eq_one _ h1)
  omega
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
