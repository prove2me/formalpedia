-- Prove2me | solution 1 for QuantumMaxCutEnergy.rank3_odd_series_ratio_0954
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T14:54:31.061669+00:00
-- url     : https://prove2.me/submissions/e88c2af7-c663-472e-9078-ac0f26e42029

import Mathlib

-- Local verified source: AGMProductCubic.lean

/-!
Elementary certification for the rank-three rounding correlation analysis.
BOFV10, Section 6, defines v(3) by (1-E₃(t))/(1-t). The intended analytic
inputs are E₃(s) ≥ (8/(3π))s + (4/(15π))s³ for s≥0, oddness, and E₃(t)≤t
for t≥0. This file proves the remaining scalar step, not those analytic
inputs or the Gaussian rounding identity.
-/

namespace AGMRoute

theorem cubic_0954 (s : ℝ) (hs : 0 ≤ s) :
    (0.954 : ℝ) * (1 + s) ≤ 1 + 0.8488 * s + 0.08488 * s ^ 3 := by
  have hsq : 0 ≤ (s - 0.645) ^ 2 * (s + 1.29) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith only [hsq, hs]

theorem negative_correlation_0954 (s e : ℝ) (hs : 0 ≤ s)
    (he : 0.8488 * s + 0.08488 * s ^ 3 ≤ e) :
    (0.954 : ℝ) ≤ (1 + e) / (1 + s) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 + s)).2
  linarith [cubic_0954 s hs]

/-- Conditional on the standard rounding-correlation identities, the cubic
bound proves a uniform 0.954 guarantee without a numerical minimizer. -/
theorem correlation_0954 (F : ℝ → ℝ)
    (hodd : ∀ t, F (-t) = -F t)
    (hnegative : ∀ s, 0 ≤ s → s ≤ 1 →
      0.8488 * s + 0.08488 * s ^ 3 ≤ F s)
    (hpositive : ∀ t, 0 ≤ t → t < 1 → F t ≤ t)
    (t : ℝ) (htlow : -1 ≤ t) (hthigh : t < 1) :
    (0.954 : ℝ) ≤ (1 - F t) / (1 - t) := by
  by_cases ht : 0 ≤ t
  · have he := hpositive t ht hthigh
    apply (le_div_iff₀ (by linarith : 0 < 1 - t)).2
    nlinarith only [he, hthigh]
  · have hs : 0 ≤ -t := by linarith
    have hs1 : -t ≤ 1 := by linarith
    have h := negative_correlation_0954 (-t) (F (-t)) hs (hnegative (-t) hs hs1)
    rw [hodd] at h
    simpa only [sub_eq_add_neg] using h


end AGMRoute


-- Local verified source: AGMProductSeries.lean

/-!
Scalar analysis of the positive odd power-series representation used in
rank-three Gaussian rounding. The source representation and its first two
coefficients are explicit hypotheses. No Gaussian identity or SDP algorithm
is claimed here.

Published formula: Briët--de Oliveira Filho--Vallentin, Theory of Computing
10(4), 2014, Lemma 2.1, https://doi.org/10.4086/toc.2014.v010a004.
Also printed as Lemma 10 / Eq. (12) of Gharibian--Parekh, APPROX 2019,
https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.31.
For r=3 it is (8/(3π))*t*₂F₁(1/2,1/2;5/2;t²).
-/

noncomputable section
open scoped BigOperators

namespace AGMRoute.ProductSeries

def correlation (c : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n, c n * t ^ (2 * n + 1)

theorem rounded_coefficients :
    (0.8488 : ℝ) ≤ 8 / (3 * Real.pi) ∧
      (0.08488 : ℝ) ≤ 4 / (15 * Real.pi) := by
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 3 * Real.pi)).2
    nlinarith [Real.pi_lt_d4]
  · apply (le_div_iff₀ (by positivity : 0 < 15 * Real.pi)).2
    nlinarith [Real.pi_lt_d4]

theorem power_le_one (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ n : ℕ, s ^ n ≤ 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      s ^ (n + 1) = s ^ n * s := pow_succ _ _
      _ ≤ 1 * s := mul_le_mul_of_nonneg_right ih hs
      _ ≤ 1 := by simpa using hs1

theorem correlation_summable (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsum : Summable c) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (fun n => c n * s ^ (2 * n + 1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hc n) (pow_nonneg hs _)) _ hsum
  intro n
  simpa using mul_le_mul_of_nonneg_left (power_le_one s hs hs1 _) (hc n)

theorem correlation_odd (c : ℕ → ℝ) (t : ℝ) :
    correlation c (-t) = -correlation c t := by
  unfold correlation
  have hterm (n : ℕ) : c n * (-t) ^ (2 * n + 1) = -(c n * t ^ (2 * n + 1)) := by
    rw [(odd_two_mul_add_one n).neg_pow]
    exact mul_neg _ _
  simp_rw [hterm]
  exact tsum_neg

theorem correlation_lower (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsum : Summable c)
    (hc0 : 8 / (3 * Real.pi) ≤ c 0) (hc1 : 4 / (15 * Real.pi) ≤ c 1)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0.8488 * s + 0.08488 * s ^ 3 ≤ correlation c s := by
  have hcs := correlation_summable c hc hsum s hs hs1
  have htwo := hcs.sum_le_tsum ({0, 1} : Finset ℕ)
    (fun n _ => mul_nonneg (hc n) (pow_nonneg hs _))
  have htwo' : c 0 * s + c 1 * s ^ 3 ≤ correlation c s := by
    simpa [correlation] using htwo
  have h0 := mul_le_mul_of_nonneg_right (rounded_coefficients.1.trans hc0) hs
  have h1 := mul_le_mul_of_nonneg_right (rounded_coefficients.2.trans hc1)
    (pow_nonneg hs 3)
  linarith

theorem correlation_upper (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsum : Summable c) (hunit : (∑' n, c n) = 1)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    correlation c s ≤ s := by
  have hcs := correlation_summable c hc hsum s hs hs1
  calc
    correlation c s ≤ ∑' n, c n * s := by
      apply hcs.tsum_le_tsum _ (hsum.mul_right s)
      intro n
      apply mul_le_mul_of_nonneg_left _ (hc n)
      rw [pow_succ]
      simpa using mul_le_mul_of_nonneg_right (power_le_one s hs hs1 (2 * n)) hs
    _ = s := by rw [tsum_mul_right, hunit, one_mul]

theorem solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsum : Summable c) (hunit : (∑' n, c n) = 1)
    (hc0 : 8 / (3 * Real.pi) ≤ c 0) (hc1 : 4 / (15 * Real.pi) ≤ c 1)
    (t : ℝ) (htlow : -1 ≤ t) (hthigh : t < 1) :
    (0.954 : ℝ) ≤ (1 - ∑' n, c n * t ^ (2 * n + 1)) / (1 - t) := by
  exact AGMRoute.correlation_0954 (correlation c) (correlation_odd c)
    (correlation_lower c hc hsum hc0 hc1)
    (fun s hs hs1 => correlation_upper c hc hsum hunit s hs (le_of_lt hs1))
    t htlow hthigh


end AGMRoute.ProductSeries


theorem solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsum : Summable c) (hunit : (∑' n, c n) = 1)
    (hc0 : 8 / (3 * Real.pi) ≤ c 0) (hc1 : 4 / (15 * Real.pi) ≤ c 1)
    (t : ℝ) (htlow : -1 ≤ t) (hthigh : t < 1) :
    (0.954 : ℝ) ≤ (1 - ∑' n, c n * t ^ (2 * n + 1)) / (1 - t) := by
  exact AGMRoute.ProductSeries.solution c hc hsum hunit hc0 hc1 t htlow hthigh

#print axioms solution
