-- Prove2me | solution 1 for PoissonDepTrials.SecondOrder.stein_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:11:39.026464+00:00
-- url     : https://prove2.me/submissions/44c3ecfc-1195-4dc7-aa7c-43dc2af95734

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

open PoissonDepTrials.SecondOrder in
theorem solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    (∀ w : ℕ, (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h) ∧
    (∀ w : ℕ, 1 ≤ w → stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)) := by
  have hl0 : lam ≠ 0 := hlam.ne'
  refine ⟨?_, ?_⟩
  · intro w
    cases w with
    | zero =>
      simp only [stein, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, pow_zero,
        zero_add, Nat.zero_sub, CharP.cast_eq_zero, zero_mul, pow_one, div_one, mul_one, one_mul]
      field_simp
      ring
    | succ n =>
      simp only [stein, Nat.add_sub_cancel, Finset.sum_range_succ (n := n + 1)]
      rw [Nat.factorial_succ n]
      push_cast
      generalize (∑ k ∈ Finset.range (n + 1), (h k - poissonExp lam h) * lam ^ k /
        (k.factorial : ℝ)) = S
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      rw [pow_succ lam (n + 1)]
      field_simp
      ring
  · intro w _
    have hE : HasSum (fun n : ℕ => lam ^ n / (n.factorial : ℝ)) (Real.exp lam) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp lam
    have hnn : ∀ k : ℕ, 0 ≤ lam ^ k / (k.factorial : ℝ) := fun k => by positivity
    have hs : Summable (fun k : ℕ => h k * (lam ^ k / (k.factorial : ℝ))) := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
        (hE.summable.mul_left M))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn k)]
      exact mul_le_mul_of_nonneg_right (hM k) (hnn k)
    have hP : poissonExp lam h = Real.exp (-lam) * ∑' k : ℕ, h k * (lam ^ k / (k.factorial : ℝ)) := by
      rw [poissonExp, ← tsum_mul_left]
      congr 1
      ext k
      ring
    have hA : HasSum (fun k : ℕ => (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)) 0 := by
      have h1 := hs.hasSum.sub (hE.mul_left (poissonExp lam h))
      have h0 : (∑' k : ℕ, h k * (lam ^ k / (k.factorial : ℝ))) - poissonExp lam h * Real.exp lam = 0 := by
        rw [hP, Real.exp_neg]
        field_simp
        ring
      rw [h0] at h1
      have hfun : (fun k : ℕ => (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)) =
          fun k => h k * (lam ^ k / (k.factorial : ℝ)) - poissonExp lam h * (lam ^ k / (k.factorial : ℝ)) := by
        funext k
        ring
      rw [hfun]
      exact h1
    have hT := (hasSum_nat_add_iff' w).mpr hA
    rw [hT.tsum_eq]
    simp only [stein]
    ring
