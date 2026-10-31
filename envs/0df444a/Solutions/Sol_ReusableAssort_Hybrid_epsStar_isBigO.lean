-- Prove2me | solution 1 for ReusableAssort.Hybrid.epsStar_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:14:49.224152+00:00
-- url     : https://prove2.me/submissions/07db24de-1dc9-4d41-b246-7af5696c8b72

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Model

open ReusableAssort.Hybrid

private lemma hfun_ge_gamma {γ x : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) : γ ≤ hfun γ x := by
  unfold hfun
  have h1 : 0 ≤ 1 - γ := by linarith [hγ.2]
  have he := Real.exp_pos (-(γ ^ 2 * x / (2 - γ)))
  have : (1 - γ) * (1 - Real.exp (-(γ ^ 2 * x / (2 - γ)))) ≤ (1 - γ) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) h1
  linarith

private lemma epsStar_le_hfun {γ x : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    epsStar x ≤ hfun γ x := by
  unfold epsStar
  refine csInf_le ⟨0, ?_⟩ ⟨γ, hγ, rfl⟩
  rintro b ⟨γ', hγ', rfl⟩
  exact (hγ'.1).trans (hfun_ge_gamma hγ')

/-- The explicit bound `ε*(x) ≤ 3 √(log x / x)` for `x ≥ 16`. -/
private lemma epsStar_bound {x : ℝ} (hx : 16 ≤ x) :
    epsStar x ≤ 3 * Real.sqrt (Real.log x / x) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL
  have hsx : 4 ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsxsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hLle : L ≤ 2 * Real.sqrt x := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [Real.log_sqrt hx0.le] at h1
    linarith
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  set γ := Real.sqrt (2 * L / x) with hγdef
  have hq : 2 * L / x ≤ 1 := by
    rw [div_le_one hx0]; nlinarith
  have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
  have hγ1 : γ ≤ 1 := by
    rw [hγdef]; calc Real.sqrt (2 * L / x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hq
      _ = 1 := Real.sqrt_one
  have hγsq : γ ^ 2 = 2 * L / x := Real.sq_sqrt (by positivity)
  have hexp : Real.exp (-(γ ^ 2 * x / (2 - γ))) ≤ 1 / x := by
    have hnum : γ ^ 2 * x = 2 * L := by rw [hγsq]; field_simp
    have h2 : L ≤ γ ^ 2 * x / (2 - γ) := by
      rw [hnum, le_div_iff₀ (by linarith)]; nlinarith
    calc Real.exp (-(γ ^ 2 * x / (2 - γ))) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / x := by rw [Real.exp_neg, hL, Real.exp_log hx0, one_div]
  have hh : hfun γ x ≤ γ + 1 / x := by
    unfold hfun
    have he := Real.exp_pos (-(γ ^ 2 * x / (2 - γ)))
    nlinarith
  have hγb : γ ≤ 2 * Real.sqrt (L / x) := by
    rw [hγdef, mul_div_assoc, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      · exact Real.sqrt_le_sqrt (by norm_num)
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  have hxb : 1 / x ≤ Real.sqrt (L / x) := by
    have hx1 : 1 / x ≤ 1 := by rw [div_le_one hx0]; linarith
    have h1x : 0 ≤ 1 / x := by positivity
    have : (1 / x) ^ 2 ≤ L / x := by
      rw [sq, div_eq_mul_one_div L x]
      nlinarith
    calc 1 / x = Real.sqrt ((1 / x) ^ 2) := (Real.sqrt_sq h1x).symm
      _ ≤ Real.sqrt (L / x) := Real.sqrt_le_sqrt this
  calc epsStar x ≤ hfun γ x := epsStar_le_hfun ⟨hγ0, hγ1⟩
    _ ≤ γ + 1 / x := hh
    _ ≤ 3 * Real.sqrt (L / x) := by linarith

theorem solution :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x ≥ x₀,
      epsStar x ≤ C * Real.sqrt (Real.log x / x) ∧
      ∀ γ, IsGammaStar x γ → γ ≤ C * Real.sqrt (Real.log x / x) := by
  refine ⟨3, 16, by norm_num, fun x hx => ⟨epsStar_bound hx, fun γ hγ => ?_⟩⟩
  calc γ ≤ hfun γ x := hfun_ge_gamma hγ.1
    _ = epsStar x := hγ.2
    _ ≤ _ := epsStar_bound hx
