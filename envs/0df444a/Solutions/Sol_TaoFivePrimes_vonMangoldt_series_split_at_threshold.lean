-- Prove2me | solution 1 for TaoFivePrimes.vonMangoldt_series_split_at_threshold
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:59:21.683868+00:00
-- url     : https://prove2.me/submissions/17def970-7a18-4249-834b-318ced4cef80

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace VMSplitCex

/-- the indicator of `{0}` -/
noncomputable def f0 : ℕ → ℂ := fun n => if n = 0 then 1 else 0

theorem inner_eq (d : ℕ) (hd : d ≠ 0) : (∑' m : ℕ, f0 (d * m)) = 1 := by
  have : (fun m : ℕ => f0 (d * m)) = fun m => if m = 0 then 1 else 0 := by
    funext m; simp [f0, hd]
  rw [this, tsum_ite_eq]

theorem lhs_zero : (∑' n : ℕ, ((Λ n : ℝ) : ℂ) * f0 n) = 0 := by
  have : (fun n : ℕ => ((Λ n : ℝ) : ℂ) * f0 n) = fun _ => 0 := by
    funext n
    by_cases h : n = 0
    · subst h; simp
    · simp [f0, h]
  rw [this, tsum_zero]

theorem first_eq :
    (∑' d : ℕ, (if d <= 2 then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f0 (d * m))) = (Real.log 2 : ℂ) := by
  rw [tsum_eq_sum (s := Finset.range 3)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [inner_eq 1 one_ne_zero, inner_eq 2 two_ne_zero]
    have h2 : (μ 2 : ℤ) = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
    simp [h2]
  · intro d hd
    simp only [Finset.mem_range, not_lt] at hd
    have : ¬ d ≤ 2 := by omega
    simp [this]

theorem second_not_summable :
    ¬ Summable (fun d : ℕ => (if 2 < d then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f0 (d * m))) := by
  intro hs
  have ht := hs.tendsto_atTop_zero
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (Real.log 2) hpos
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 3)
  have h := hN p (by omega)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp2 : 2 < p := by omega
  rw [inner_eq p hp0, ArithmeticFunction.moebius_apply_prime hp] at h
  simp only [hp2, if_true, dist_zero_right] at h
  have hlog : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ p))
  have : ‖(1 : ℂ) * -((((-1 : ℤ) : ℝ) : ℂ) * (Real.log p : ℂ)) * 1‖ = Real.log p := by
    simp only [one_mul, mul_one, Int.cast_neg, Int.cast_one, Complex.ofReal_neg,
      Complex.ofReal_one, neg_mul, neg_neg, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))
  push_cast at h this
  linarith

theorem second_eq :
    (∑' d : ℕ, (if 2 < d then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f0 (d * m))) = 0 :=
  tsum_eq_zero_of_not_summable second_not_summable

end VMSplitCex

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius in
theorem solution : ¬ (∀ (f : ℕ → ℂ) (U : ℕ)
    (hfin : Exists fun N0 : ℕ => forall n : ℕ, N0 < n -> f n = 0),
    (∑' n : ℕ, ((Λ n : ℝ) : ℂ) * f n) =
      (∑' d : ℕ, (if d <= U then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f (d * m))) +
      (∑' d : ℕ, (if U < d then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f (d * m)))) := by
  intro H
  have h := H VMSplitCex.f0 2 ⟨0, fun n hn => by simp [VMSplitCex.f0]; omega⟩
  rw [VMSplitCex.lhs_zero, VMSplitCex.first_eq, VMSplitCex.second_eq, add_zero] at h
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h' : Real.log 2 = 0 := by exact_mod_cast h.symm
  linarith
