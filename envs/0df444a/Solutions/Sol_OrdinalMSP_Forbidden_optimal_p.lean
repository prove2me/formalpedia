-- Prove2me | solution 1 for OrdinalMSP.Forbidden.optimal_p
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:01:41.459051+00:00
-- url     : https://prove2.me/submissions/918f390d-56fa-484c-9858-d2b92382a90d

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

open OrdinalMSP.Forbidden

theorem solution (k : ℕ) (hk : 1 ≤ k) (g : ℝ → ℝ)
    (hg : ∀ p, g p = if k = 1 then -p * Real.log p else (p - p ^ k) / ((k : ℝ) - 1)) :
    pK k ∈ Set.Ioc 0 1 ∧ g (pK k) = 1 / alphaK k ∧ ∀ p ∈ Set.Ioc (0 : ℝ) 1, g p ≤ g (pK k) := by
  by_cases hk1 : k = 1
  · subst hk1
    have hpK : pK 1 = Real.exp (-1) := by simp [pK]
    have haK : alphaK 1 = Real.exp 1 := by simp [alphaK]
    have hgK : g (Real.exp (-1)) = Real.exp (-1) := by
      rw [hg]; simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hpK]; refine ⟨Real.exp_pos _, ?_⟩
      rw [Real.exp_le_one_iff]; norm_num
    · rw [hpK, haK, hgK, Real.exp_neg, one_div]
    · intro p ⟨hp0, hp1⟩
      rw [hpK, hgK, hg]; simp only [if_true]
      -- -p log p ≤ e^{-1}
      have hx : 0 < 1 / (Real.exp 1 * p) := by positivity
      have h := Real.log_le_sub_one_of_pos hx
      rw [one_div, Real.log_inv, Real.log_mul (Real.exp_pos 1).ne' hp0.ne', Real.log_exp] at h
      have hinv : (Real.exp 1 * p)⁻¹ * p = Real.exp (-1) := by
        rw [Real.exp_neg]; field_simp
      nlinarith [hinv]
  · have hk2 : 2 ≤ k := by omega
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hkpos : (0 : ℝ) < k := by linarith
    have hk1R : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    set c : ℝ := (k : ℝ) ^ (-(1 / ((k : ℝ) - 1))) with hc
    have hpK : pK k = c := by simp [pK, hk1, hc]
    have hcpos : 0 < c := Real.rpow_pos_of_pos hkpos _
    have hc1 : c ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      have : 0 < 1 / ((k : ℝ) - 1) := by positivity
      linarith
    have hck1 : c ^ (k - 1) = 1 / (k : ℝ) := by
      rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this, neg_mul, one_div_mul_cancel hk1R.ne', Real.rpow_neg_one, one_div]
    have hck : c ^ k = c * (1 / (k : ℝ)) := by
      rw [← hck1, ← pow_succ']; congr 1; omega
    have hgK : g c = c / k := by
      rw [hg, if_neg hk1, hck]; field_simp
    have haK : 1 / alphaK k = c / k := by
      simp only [alphaK, if_neg hk1]
      rw [one_div, ← Real.rpow_neg hkpos.le]
      have e1 : c / k = (k:ℝ) ^ (-(1 / ((k:ℝ) - 1)) - 1) := by
        rw [Real.rpow_sub hkpos, Real.rpow_one]
      rw [e1]
      congr 1; field_simp; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hpK]; exact ⟨hcpos, hc1⟩
    · rw [hpK, hgK, haK]
    · intro p ⟨hp0, hp1⟩
      rw [hpK, hgK, hg, if_neg hk1]
      -- Bernoulli: p^k ≥ c^k + k c^{k-1} (p - c)
      have hb := one_add_mul_le_pow (a := p / c - 1) (by
        have : 0 ≤ p / c := by positivity
        linarith) k
      have h1 : (1 + (p / c - 1)) = p / c := by ring
      rw [h1, div_pow] at hb
      have hckpos : 0 < c ^ k := pow_pos hcpos k
      have hb2 : c ^ k * (1 + (k : ℝ) * (p / c - 1)) ≤ p ^ k := by
        rw [le_div_iff₀ hckpos] at hb; linarith
      have hb3 : c ^ k * (1 + (k : ℝ) * (p / c - 1)) = c ^ k + (p - c) := by
        rw [hck]; field_simp
      rw [hb3] at hb2
      rw [div_le_div_iff₀ hk1R hkpos]
      have : c - c ^ k = c / k * ((k : ℝ) - 1) := by rw [hck]; field_simp
      have h2 : p - p ^ k ≤ c / k * ((k : ℝ) - 1) := by linarith
      have h3 : (p - p ^ k) * k ≤ c / k * ((k : ℝ) - 1) * k :=
        mul_le_mul_of_nonneg_right h2 hkpos.le
      have h4 : c / k * ((k : ℝ) - 1) * k = c * ((k : ℝ) - 1) := by field_simp
      linarith
