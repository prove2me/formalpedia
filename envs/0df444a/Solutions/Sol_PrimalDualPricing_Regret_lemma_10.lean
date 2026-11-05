-- Prove2me | solution 1 for PrimalDualPricing.Regret.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:47:22.35471+00:00
-- url     : https://prove2.me/submissions/17d5fbcf-cf89-4e39-a225-5a9c92597097

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution (lam : NNReal) :
    Integrable (fun x : ℕ => |(x : ℝ) - lam|) (poissonMeasure lam) ∧
    ∫ x, |(x : ℝ) - lam| ∂(poissonMeasure lam) ≤ Real.sqrt lam := by
  set r : ℝ := (lam : ℝ) with hr
  have hr0 : 0 ≤ r := lam.2
  set p : ℕ → ℝ := fun n => Real.exp (-r) * r ^ n / (n.factorial) with hp
  have hp0 : ∀ n, 0 ≤ p n := fun n => by simp only [hp]; positivity
  have h0 : HasSum p 1 := hasSum_one_poissonMeasure lam
  -- first factorial moment
  have h1 : HasSum (fun n : ℕ => p n * (n : ℝ)) r := by
    have hs : HasSum (fun n : ℕ => p (n + 1) * ((n + 1 : ℕ) : ℝ)) r := by
      have e : (fun n : ℕ => p (n + 1) * ((n + 1 : ℕ) : ℝ)) = fun n => r * p n := by
        funext n
        simp only [hp, Nat.factorial_succ, Nat.cast_mul, pow_succ]
        have : (n.factorial : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
      rw [e]; simpa using h0.mul_left r
    have := (hasSum_nat_add_iff (f := fun n : ℕ => p n * (n : ℝ)) 1).mp hs
    simpa using this
  -- second factorial moment
  have h2 : HasSum (fun n : ℕ => p n * ((n : ℝ) * ((n : ℝ) - 1))) (r ^ 2) := by
    have hs : HasSum (fun n : ℕ => p (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)))
        (r ^ 2) := by
      have e : (fun n : ℕ => p (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)))
          = fun n => r ^ 2 * p n := by
        funext n
        simp only [hp, Nat.factorial_succ, Nat.cast_mul, pow_succ]
        have : (n.factorial : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      rw [e]; simpa using h0.mul_left (r ^ 2)
    have := (hasSum_nat_add_iff (f := fun n : ℕ => p n * ((n : ℝ) * ((n : ℝ) - 1))) 2).mp hs
    simpa [Finset.sum_range_succ] using this
  -- variance
  have hV : HasSum (fun n : ℕ => p n * ((n : ℝ) - r) ^ 2) r := by
    have H := ((h2.add h1).sub (h1.mul_left (2 * r))).add (h0.mul_left (r ^ 2))
    have e1 : r ^ 2 + r - 2 * r * r + r ^ 2 * 1 = r := by ring
    rw [e1] at H
    convert H using 1
    all_goals first | rfl | (funext n; ring)
  -- AM-GM bound with parameter s > 0
  have hbound : ∀ s : ℝ, 0 < s →
      HasSum (fun n : ℕ => p n * (((n : ℝ) - r) ^ 2 / (2 * s) + s / 2)) (r / (2 * s) + s / 2) := by
    intro s hs
    have H := (hV.div_const (2 * s)).add (h0.mul_left (s / 2))
    rw [mul_one] at H
    convert H using 1
    all_goals first | rfl | (funext n; ring)
  have hpt : ∀ s : ℝ, 0 < s → ∀ x : ℝ, |x| ≤ x ^ 2 / (2 * s) + s / 2 := by
    intro s hs x
    rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|x| - s), sq_abs x, abs_nonneg x]
  have hsum : Summable (fun n : ℕ => p n * |(n : ℝ) - r|) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hp0 n) (abs_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hpt 1 one_pos _) (hp0 n)) (hbound 1 one_pos).summable
  have hint : Integrable (fun x : ℕ => |(x : ℝ) - lam|) (poissonMeasure lam) := by
    rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs, abs_abs] using hsum
  refine ⟨hint, ?_⟩
  rw [integral_poissonMeasure' hint]
  simp only [smul_eq_mul]
  change ∑' n : ℕ, p n * |(n : ℝ) - r| ≤ Real.sqrt r
  rcases hr0.eq_or_lt with h | h
  · have : (fun n : ℕ => p n * |(n : ℝ) - r|) = fun n : ℕ => p n * (n : ℝ) := by
      funext n; rw [← h, sub_zero, Nat.abs_cast]
    rw [this, h1.tsum_eq, ← h, Real.sqrt_zero]
  · set s := Real.sqrt r with hsdef
    have hs : 0 < s := Real.sqrt_pos.mpr h
    have hss : s * s = r := Real.mul_self_sqrt hr0
    calc ∑' n : ℕ, p n * |(n : ℝ) - r| ≤ r / (2 * s) + s / 2 :=
          hasSum_le (fun n => mul_le_mul_of_nonneg_left (hpt s hs _) (hp0 n))
            hsum.hasSum (hbound s hs)
      _ = s := by
          rw [← hss]; field_simp; ring
