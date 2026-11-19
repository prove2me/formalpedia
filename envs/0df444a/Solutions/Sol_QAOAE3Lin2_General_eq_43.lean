-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_43
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:13:34.394595+00:00
-- url     : https://prove2.me/submissions/108ec233-3c21-4aaf-be76-f46255a390cb

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

open QAOAE3Lin2.General

private lemma exp_21_10_lt : Real.exp (21 / 10 : ℝ) < (10 / 9 : ℝ) ^ 20 := by
  have hb := Real.exp_bound (x := (1 / 10 : ℝ)) (n := 4) (by norm_num) (by norm_num)
  have h1 : |Real.exp (1 / 10) - (1 + 1 / 10 + (1 / 10) ^ 2 / 2 + (1 / 10) ^ 3 / 6)| ≤
      |(1 / 10 : ℝ)| ^ 4 * (5 / (24 * 4)) := by
    simpa [Finset.sum_range_succ, Nat.factorial] using hb
  have h2 : Real.exp (1 / 10 : ℝ) < 11052 / 10000 := by
    have := (abs_le.mp h1).2
    norm_num at this
    linarith
  have hpow : Real.exp (1 / 10 : ℝ) ^ 21 < (11052 / 10000 : ℝ) ^ 21 :=
    pow_lt_pow_left₀ h2 (Real.exp_pos _).le (by norm_num)
  have hnum : (11052 / 10000 : ℝ) ^ 21 < (10 / 9 : ℝ) ^ 20 := by norm_num
  have hexp : Real.exp (21 / 10 : ℝ) = Real.exp (1 / 10 : ℝ) ^ 21 := by
    rw [← Real.exp_nat_mul]
    norm_num
  linarith

private lemma nine_tenths_pow_le {k : ℕ} {L : ℝ} (hL : 0 ≤ L) (hk : 5 * L ≤ (k : ℝ)) :
    (9 / 10 : ℝ) ^ (k + 2) ≤ Real.exp (-21 / 40 * L) := by
  have hlog : Real.log (9 / 10 : ℝ) < -21 / 200 := by
    have hlt : Real.exp (21 / 10 : ℝ) < (10 / 9 : ℝ) ^ 20 := exp_21_10_lt
    have h1 : (21 / 10 : ℝ) < Real.log ((10 / 9 : ℝ) ^ 20) :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr hlt
    rw [Real.log_pow] at h1
    have hinv : Real.log (9 / 10 : ℝ) = -Real.log (10 / 9 : ℝ) := by
      rw [← Real.log_inv]; norm_num
    linarith
  have hk_pos : (9 / 10 : ℝ) ^ (k + 2) ≤ (9 / 10 : ℝ) ^ (5 * L) := by
    rw [← Real.rpow_natCast (9 / 10 : ℝ) (k + 2)]
    refine Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ?_
    push_cast
    linarith
  have hrpow : (9 / 10 : ℝ) ^ (5 * L) = Real.exp (Real.log (9 / 10) * (5 * L)) :=
    Real.rpow_def_of_pos (by norm_num) (5 * L)
  have hexp : Real.exp (Real.log (9 / 10) * (5 * L)) ≤ Real.exp (-21 / 40 * L) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  exact hk_pos.trans (hrpow ▸ hexp)

theorem solution :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∃ k : ℕ, Odd k ∧ 5 * Real.log D ≤ k ∧
      (k : ℝ) ≤ 5 * Real.log D + 2 ∧
      1 / (101 * Real.sqrt D * Real.log D) < 1 / (20 * Real.sqrt D * k) - (9 / 10 : ℝ) ^ (k + 2) := by
  refine ⟨Nat.ceil (Real.exp 50000000), fun D hD => ?_⟩
  have hD_ge : Real.exp 50000000 ≤ (D : ℝ) := (Nat.ceil_le).mp hD
  have hD_pos : (0 : ℝ) < D := lt_of_lt_of_le (Real.exp_pos 50000000) hD_ge
  have hL : (50000000 : ℝ) ≤ Real.log D := by
    rw [← Real.exp_le_exp, Real.exp_log hD_pos]
    exact hD_ge
  have hL_pos : 0 < Real.log D := by linarith
  let m : ℕ := Nat.floor (5 * Real.log D)
  have hm_le : (m : ℝ) ≤ 5 * Real.log D := Nat.floor_le (by positivity)
  have hm_lt : 5 * Real.log D < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  let k : ℕ := if Odd m then m + 2 else m + 1
  have hk_odd : Odd k := by
    dsimp only [k]
    split_ifs with hm
    · exact hm.add_even (by decide)
    · rw [Nat.not_odd_iff_even] at hm
      exact hm.add_odd (by decide)
  have hk_ge : 5 * Real.log D ≤ (k : ℝ) := by
    dsimp only [k]
    split_ifs with hm <;> push_cast <;> linarith
  have hk_le : (k : ℝ) ≤ 5 * Real.log D + 2 := by
    dsimp only [k]
    split_ifs with hm <;> push_cast <;> linarith
  refine ⟨k, hk_odd, hk_ge, hk_le, ?_⟩
  have hsqrt_pos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD_pos
  have hk_pos : (0 : ℝ) < k := by linarith
  have hgap : 1 / (15000 * Real.sqrt D * Real.log D) ≤
      1 / (20 * Real.sqrt D * k) - 1 / (101 * Real.sqrt D * Real.log D) := by
    have hden1 : 0 < 20 * Real.sqrt D * (k : ℝ) := by positivity
    have hden2 : 0 < 101 * Real.sqrt D * Real.log D := by positivity
    have hden3 : 0 < 15000 * Real.sqrt D * Real.log D := by positivity
    rw [div_sub_div _ _ hden1.ne' hden2.ne', le_div_iff₀ (mul_pos hden1 hden2)]
    have hk_ub : 20 * (k : ℝ) ≤ 100.2 * Real.log D := by linarith
    have h1 : 101 * Real.sqrt D * Real.log D - 20 * Real.sqrt D * (k : ℝ) ≥
        0.8 * Real.sqrt D * Real.log D := by nlinarith [hsqrt_pos]
    have hmul : 1 / (15000 * Real.sqrt D * Real.log D) *
        ((20 * Real.sqrt D * (k : ℝ)) * (101 * Real.sqrt D * Real.log D)) ≤
        0.8 * Real.sqrt D * Real.log D := by
      have hLHS : 1 / (15000 * Real.sqrt D * Real.log D) *
          ((20 * Real.sqrt D * (k : ℝ)) * (101 * Real.sqrt D * Real.log D)) =
          (2020 * (k : ℝ) / 15000) * Real.sqrt D := by
        field_simp
        norm_num
      rw [hLHS]
      have hk_ub2 : (k : ℝ) ≤ 5.001 * Real.log D := by linarith
      nlinarith
    nlinarith
  have htail : (9 / 10 : ℝ) ^ (k + 2) < 1 / (15000 * Real.sqrt D * Real.log D) := by
    have h1 := nine_tenths_pow_le hL_pos.le hk_ge
    have hsqrt_eq : Real.sqrt D = Real.exp (Real.log D / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hD_pos]
      ring_nf
    have hexp_lb : (Real.log D / 40) ^ 2 / 2 ≤ Real.exp (Real.log D / 40) := by
      have hs := Real.sum_le_exp_of_nonneg (show 0 ≤ Real.log D / 40 by linarith) 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
        Nat.factorial, Nat.cast_one, div_one] at hs
      have hpos1 : (0 : ℝ) ≤ 1 + Real.log D / 40 := by linarith
      linarith
    have hprod : 15000 * Real.sqrt D * Real.log D * Real.exp (-21 / 40 * Real.log D) < 1 := by
      rw [hsqrt_eq]
      have hexp_mul : 15000 * Real.exp (Real.log D / 2) * Real.log D * Real.exp (-21 / 40 * Real.log D) =
          15000 * Real.log D * (Real.exp (Real.log D / 2) * Real.exp (-21 / 40 * Real.log D)) := by ring
      rw [hexp_mul, ← Real.exp_add]
      have heq : Real.log D / 2 + -21 / 40 * Real.log D = -(Real.log D / 40) := by ring
      rw [heq, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
      nlinarith
    have hpos_prod : 0 < 15000 * Real.sqrt D * Real.log D := by positivity
    have hlt_inv : Real.exp (-21 / 40 * Real.log D) < 1 / (15000 * Real.sqrt D * Real.log D) :=
      (lt_div_iff₀ hpos_prod).mpr (by linarith)
    exact lt_of_le_of_lt h1 hlt_inv
  linarith
