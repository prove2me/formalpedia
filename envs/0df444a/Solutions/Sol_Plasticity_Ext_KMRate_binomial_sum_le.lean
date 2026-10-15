-- Prove2me | solution 1 for Plasticity.Ext.KMRate.binomial_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T17:55:30.107781+00:00
-- url     : https://prove2.me/submissions/920ff68a-88b7-48aa-ac5c-71724902ae6b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Scalar part of the Cominetti–Soto–Vaisman rate (Israel J. Math. 199 (2014), Proposition 8):
for `0 ≤ u ≤ 1/2`,
`√(n u) · ∑_m C(n,m) u^m (1-u)^(n-m) C(m, ⌊m/2⌋)/2^m ≤ √(2/π)`.

Route: `C(m,⌊m/2⌋)/2^m = (1/π) ∫₀^π (1 + cos t) cos^m t dt`, the binomial theorem under the
integral, the bound `(1 + cos t)(1 - u + u cos t)^n ≤ 2 cos(t/2) exp(-2nu sin²(t/2))`, the
substitution `s = sin(t/2)` and the Gaussian integral.
-/

open Real intervalIntegral MeasureTheory Set

namespace Sol_Plasticity_Ext_KMRate_binomial_sum_le

/-- `J m = ∫₀^π cos^m t dt`. -/
noncomputable def J (m : ℕ) : ℝ := ∫ x in (0 : ℝ)..π, cos x ^ m

lemma J_zero : J 0 = π := by simp [J]

lemma J_one : J 1 = 0 := by simp [J, integral_cos]

lemma J_add_two (m : ℕ) : J (m + 2) = (m + 1) / (m + 2) * J m := by
  unfold J
  rw [integral_cos_pow]
  simp

lemma J_even (k : ℕ) : J (2 * k) = π * (Nat.centralBinom k : ℝ) / 4 ^ k := by
  induction k with
  | zero => simp [J_zero]
  | succ k ih =>
    have h1 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h1, J_add_two, ih]
    have h3 : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
        = 2 * (2 * k + 1) * Nat.centralBinom k := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hcb : (Nat.centralBinom (k + 1) : ℝ)
        = 2 * (2 * k + 1) * Nat.centralBinom k / (k + 1) := by
      field_simp; linarith [h3]
    rw [hcb]; push_cast; field_simp; ring

lemma J_odd (k : ℕ) : J (2 * k + 1) = 0 := by
  induction k with
  | zero => simpa using J_one
  | succ k ih =>
    have h1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [h1, J_add_two, ih, mul_zero]

/-- `C(m, ⌊m/2⌋)/2^m = (J m + J (m+1))/π`. -/
lemma F_eq (m : ℕ) : ((m.choose (m / 2) : ℝ) / 2 ^ m) = (J m + J (m + 1)) / π := by
  have hpi : π ≠ 0 := pi_pos.ne'
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hk : 2 * k / 2 = k := by omega
    rw [hk, J_even, J_odd, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    field_simp
    norm_num
    ring
  · have hk : (2 * k + 1) / 2 = k := by omega
    have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    rw [hk, h2, J_even, J_odd]
    have hc : Nat.centralBinom (k + 1) = 2 * (2 * k + 1).choose k := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, Nat.choose_succ_succ, Nat.choose_symm_half]; ring
    rw [hc]; push_cast
    rw [pow_succ, pow_mul]
    field_simp
    norm_num
    ring

/-- `C(m, ⌊m/2⌋)/2^m = (1/π) ∫₀^π (1 + cos t) cos^m t dt`. -/
lemma F_integral (m : ℕ) : ((m.choose (m / 2) : ℝ) / 2 ^ m) =
    (∫ x in (0 : ℝ)..π, (1 + cos x) * cos x ^ m) / π := by
  rw [F_eq]
  congr 1
  unfold J
  rw [← intervalIntegral.integral_add]
  · congr 1; ext x; ring
  · exact (continuous_cos.pow m).intervalIntegrable _ _
  · exact (continuous_cos.pow _).intervalIntegrable _ _

/-- The binomial sum as an integral. -/
lemma sum_eq (n : ℕ) (u : ℝ) :
    ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℝ) * u ^ m * (1 - u) ^ (n - m) * ((m.choose (m / 2) : ℝ) / 2 ^ m)
      = (∫ x in (0 : ℝ)..π, (1 + cos x) * (u * cos x + (1 - u)) ^ n) / π := by
  simp_rw [F_integral]
  have hx : ∀ x, (1 + cos x) * (u * cos x + (1 - u)) ^ n
      = ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℝ) * u ^ m * (1 - u) ^ (n - m) * ((1 + cos x) * cos x ^ m) := by
    intro x
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    ring
  simp_rw [hx]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [intervalIntegral.integral_const_mul]
    ring
  · intro m _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Pointwise bound on the integrand. -/
lemma integrand_le (n : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (x : ℝ)
    (hx : x ∈ Icc 0 π) :
    (1 + cos x) * (u * cos x + (1 - u)) ^ n
      ≤ 4 * (exp (-(2 * n * u) * sin (x / 2) ^ 2) * (cos (x / 2) / 2)) := by
  have hc : cos x = 1 - 2 * sin (x / 2) ^ 2 := by
    rw [← cos_two_mul_eq_one_sub]; ring_nf
  have hc' : cos x = 2 * cos (x / 2) ^ 2 - 1 := by
    rw [← cos_two_mul]; ring_nf
  have hcos0 : 0 ≤ cos (x / 2) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, pi_pos], by linarith [hx.2]⟩
  have hcos1 : cos (x / 2) ≤ 1 := cos_le_one _
  have hs1 : sin (x / 2) ^ 2 ≤ 1 := sin_sq_le_one _
  have hs0 : 0 ≤ sin (x / 2) ^ 2 := sq_nonneg _
  set s := sin (x / 2) ^ 2
  have hbase : u * cos x + (1 - u) = 1 - 2 * u * s := by rw [hc]; ring
  have hb0 : 0 ≤ 1 - 2 * u * s := by nlinarith
  have hb1 : 1 - 2 * u * s ≤ exp (-(2 * u * s)) := by
    linarith [add_one_le_exp (-(2 * u * s))]
  have hpow : (1 - 2 * u * s) ^ n ≤ exp (-(2 * n * u) * s) := by
    calc (1 - 2 * u * s) ^ n ≤ (exp (-(2 * u * s))) ^ n := pow_le_pow_left₀ hb0 hb1 n
      _ = exp (-(2 * n * u) * s) := by rw [← exp_nat_mul]; ring_nf
  have h1 : 1 + cos x ≤ 2 * cos (x / 2) := by rw [hc']; nlinarith
  rw [hbase]
  calc (1 + cos x) * (1 - 2 * u * s) ^ n ≤ (2 * cos (x / 2)) * exp (-(2 * n * u) * s) :=
        mul_le_mul h1 hpow (pow_nonneg hb0 n) (by positivity)
    _ = _ := by ring

/-- The substituted Gaussian bound. -/
lemma integral_le (a : ℝ) (ha : 0 < a) :
    ∫ x in (0 : ℝ)..π, 4 * (exp (-a * sin (x / 2) ^ 2) * (cos (x / 2) / 2))
      ≤ 2 * √(π / a) := by
  rw [intervalIntegral.integral_const_mul]
  have hsub : ∫ x in (0 : ℝ)..π, exp (-a * sin (x / 2) ^ 2) * (cos (x / 2) / 2)
      = ∫ y in (0 : ℝ)..1, exp (-a * y ^ 2) := by
    have := integral_comp_mul_deriv (a := 0) (b := π) (f := fun x => sin (x / 2))
      (f' := fun x => cos (x / 2) / 2) (g := fun y => exp (-a * y ^ 2)) ?_ ?_ ?_
    · simpa using this
    · intro x _
      have := ((hasDerivAt_id x).div_const 2).sin
      simpa [div_eq_mul_inv] using this
    · exact Continuous.continuousOn (by fun_prop)
    · fun_prop
  rw [hsub]
  have hle : ∫ y in (0 : ℝ)..1, exp (-a * y ^ 2) ≤ ∫ y in Ioi (0 : ℝ), exp (-a * y ^ 2) := by
    rw [integral_of_le zero_le_one]
    apply setIntegral_mono_set
    · exact (integrable_exp_neg_mul_sq ha).integrableOn
    · exact Filter.Eventually.of_forall (fun y => (exp_pos _).le)
    · exact Ioc_subset_Ioi_self.eventuallyLE
  rw [integral_gaussian_Ioi] at hle
  linarith

end Sol_Plasticity_Ext_KMRate_binomial_sum_le

open Sol_Plasticity_Ext_KMRate_binomial_sum_le in
theorem solution (n : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Real.sqrt (n * u) * ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℝ) * u ^ m * (1 - u) ^ (n - m) * ((m.choose (m / 2) : ℝ) / 2 ^ m)
      ≤ Real.sqrt (2 / Real.pi) := by
  rw [sum_eq]
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ n * u by positivity) with h | h
  · rw [← h]; simp; positivity
  · set a : ℝ := 2 * n * u with ha_def
    have ha : 0 < a := by rw [ha_def]; linarith
    have hI : ∫ x in (0 : ℝ)..π, (1 + cos x) * (u * cos x + (1 - u)) ^ n
        ≤ 2 * √(π / a) := by
      calc _ ≤ ∫ x in (0 : ℝ)..π, 4 * (exp (-a * sin (x / 2) ^ 2) * (cos (x / 2) / 2)) := by
            apply integral_mono_on pi_pos.le
            · exact Continuous.intervalIntegrable (by fun_prop) _ _
            · exact Continuous.intervalIntegrable (by fun_prop) _ _
            · intro x hx
              exact integrand_le n u hu0 hu1 x hx
        _ ≤ _ := integral_le a ha
    have hpi := pi_pos
    have hkey : √(n * u) * (2 * √(π / a) / π) = √(2 / π) := by
      have h1 : √(n * u) * √(π / a) = √(π / 2) := by
        rw [← sqrt_mul h.le]
        congr 1
        rw [ha_def]; field_simp
        exact div_self h.ne'
      have h2 : √(n * u) * (2 * √(π / a) / π) = 2 * √(π / 2) / π := by
        rw [← h1]; ring
      rw [h2, eq_comm, sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      have h3 : √(π / 2) * √(π / 2) = π / 2 := mul_self_sqrt (by positivity)
      field_simp
      nlinarith [h3]
    rw [← hkey]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hI hpi.le) (sqrt_nonneg _)
