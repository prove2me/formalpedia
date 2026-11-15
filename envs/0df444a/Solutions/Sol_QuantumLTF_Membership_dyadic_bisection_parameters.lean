-- Prove2me | solution 1 for QuantumLTF.Membership.dyadic_bisection_parameters
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T04:13:19.427852+00:00
-- url     : https://prove2.me/submissions/9a41e2d9-70d4-459a-947d-00fd4b6381c9

import Mathlib

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ q : ℕ,
        ((q + 2 : ℕ) : ℝ) ≤ C * Real.log ((2 : ℝ) ^ m / ζ) ∧
        ((m + q + 2 : ℕ) : ℝ) ≤ C * Real.log ((2 : ℝ) ^ m / ζ) ∧
        2 * (2 : ℝ) ^ m / (2 : ℝ) ^ (q + 1) ≤ ζ := by
  refine ⟨10, by norm_num, ?_⟩
  intro m hm ζ hζ hζ'
  let r : ℝ := -Real.log ζ / Real.log 2
  let k : ℕ := ⌈r⌉₊
  have hlog2 : (0 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (0 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  have hlogζ : Real.log ζ < 0 := Real.log_neg hζ hζ'
  have hr : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (neg_nonneg.mpr hlogζ.le) hlog2.le
  have hrk : r ≤ (k : ℝ) := Nat.le_ceil r
  have hkr : (k : ℝ) < r + 1 := Nat.ceil_lt_add_one hr
  have hlogeq : Real.log ((2 : ℝ) ^ m / ζ) =
      (m : ℝ) * Real.log 2 - Real.log ζ := by
    rw [Real.log_div (by positivity) (ne_of_gt hζ), Real.log_pow]
  have htarget : Real.log ((2 : ℝ) ^ m / ζ) =
      Real.log 2 * ((m : ℝ) + r) := by
    rw [hlogeq]
    dsimp [r]
    field_simp
    ring
  refine ⟨m + k, ?_, ?_, ?_⟩
  · rw [htarget]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  · rw [htarget]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  · have hlogbound : -(k : ℝ) * Real.log 2 ≤ Real.log ζ := by
      dsimp [r] at hrk
      have hklog := (div_le_iff₀ hlog2).mp hrk
      nlinarith
    have hexp : Real.exp (-(k : ℝ) * Real.log 2) ≤ ζ := by
      rw [← Real.exp_log hζ]
      exact Real.exp_le_exp.mpr hlogbound
    have hpow : Real.exp (-(k : ℝ) * Real.log 2) = 1 / (2 : ℝ) ^ k := by
      rw [show -(k : ℝ) * Real.log 2 = -((k : ℝ) * Real.log 2) by ring]
      rw [Real.exp_neg]
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp [div_eq_mul_inv]
    rw [hpow] at hexp
    calc
      2 * (2 : ℝ) ^ m / (2 : ℝ) ^ (m + k + 1) = 1 / (2 : ℝ) ^ k := by
        rw [pow_add, pow_succ]
        field_simp
        ring
      _ ≤ ζ := hexp
