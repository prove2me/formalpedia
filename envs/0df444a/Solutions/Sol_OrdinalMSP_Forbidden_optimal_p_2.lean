-- Prove2me | solution 2 for OrdinalMSP.Forbidden.optimal_p
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:07:50.677493+00:00
-- url     : https://prove2.me/submissions/008efc1e-5470-4984-a6d6-561a08e0fa1f

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting
set_option autoImplicit false

open OrdinalMSP.Forbidden

lemma uu_k1 (p : ℝ) (hp : 0 < p) : -p * Real.log p ≤ Real.exp (-1) := by
  have hx : 0 < (Real.exp 1 * p)⁻¹ := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  rw [Real.log_inv, Real.log_mul (Real.exp_pos 1).ne' hp.ne', Real.log_exp] at h
  have h2 : (Real.exp 1 * p)⁻¹ = Real.exp (-1) / p := by
    rw [Real.exp_neg]; field_simp
  rw [h2] at h
  have h3 : -(1 + Real.log p) ≤ Real.exp (-1) / p - 1 := h
  have h4 : -Real.log p ≤ Real.exp (-1) / p := by linarith
  have := mul_le_mul_of_nonneg_left h4 hp.le
  calc -p * Real.log p = p * (-Real.log p) := by ring
    _ ≤ p * (Real.exp (-1) / p) := this
    _ = Real.exp (-1) := by field_simp

theorem solution (k : ℕ) (hk : 1 ≤ k) (g : ℝ → ℝ)
    (hg : ∀ p, g p = if k = 1 then -p * Real.log p else (p - p ^ k) / ((k : ℝ) - 1)) :
    pK k ∈ Set.Ioc 0 1 ∧ g (pK k) = 1 / alphaK k ∧ ∀ p ∈ Set.Ioc (0 : ℝ) 1, g p ≤ g (pK k) := by
  by_cases hk1 : k = 1
  · subst hk1
    have hp : pK 1 = Real.exp (-1) := by simp [pK]
    have ha : alphaK 1 = Real.exp 1 := by simp [alphaK]
    refine ⟨?_, ?_, ?_⟩
    · rw [hp]
      refine ⟨Real.exp_pos _, ?_⟩
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by norm_num)
    · rw [hg, hp, ha]
      simp [Real.exp_neg]
    · intro p hp'
      rw [hg, hg, hp]
      simp only [if_true]
      have := uu_k1 p hp'.1
      have e : -Real.exp (-1) * Real.log (Real.exp (-1)) = Real.exp (-1) := by
        rw [Real.log_exp]; ring
      rw [e]; exact this
  · have hk2 : 2 ≤ k := by omega
    set K : ℝ := (k : ℝ) with hKdef
    have hK2 : 2 ≤ K := by rw [hKdef]; exact_mod_cast hk2
    have hKpos : 0 < K := by linarith
    have ha : 0 < K - 1 := by linarith
    have hpK : pK k = K ^ (-(1 / (K - 1))) := by simp [pK, hk1, hKdef]
    have hαK : alphaK k = K ^ (K / (K - 1)) := by simp [alphaK, hk1, hKdef]
    set P := pK k with hP
    have hPpos : 0 < P := by rw [hpK]; exact Real.rpow_pos_of_pos hKpos _
    have hP1 : P ≤ 1 := by
      rw [hpK]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      have : 0 < 1 / (K - 1) := by positivity
      linarith
    -- P^(k-1) = 1/K
    have hPk : P ^ (k - 1) = 1 / K := by
      rw [hpK, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
      have : (↑(k - 1) : ℝ) = K - 1 := by
        rw [Nat.cast_sub hk]; simp [hKdef]
      rw [this]
      have : -(1 / (K - 1)) * (K - 1) = -1 := by field_simp
      rw [this, Real.rpow_neg_one]; simp
    have hPk' : P ^ k = P / K := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ, hPk]
      ring
    have hgk : ∀ p, g p = (p - p ^ k) / (K - 1) := by
      intro p; rw [hg p, if_neg hk1]
    have hval : g P = 1 / alphaK k := by
      rw [hgk, hPk', hαK]
      -- (P - P/K)/(K-1) = P/K ; and P/K = 1 / K^(K/(K-1))
      have e1 : (P - P / K) / (K - 1) = P / K := by field_simp <;> ring
      rw [e1, hpK]
      have : K ^ (K / (K - 1)) = K ^ (1 / (K - 1)) * K := by
        have : K / (K - 1) = 1 / (K - 1) + 1 := by field_simp; ring
        rw [this, Real.rpow_add hKpos, Real.rpow_one]
      rw [this, Real.rpow_neg hKpos.le]
      field_simp
    refine ⟨⟨hPpos, hP1⟩, hval, ?_⟩
    intro p hp
    rw [hgk, hgk]
    apply div_le_div_of_nonneg_right _ ha.le
    -- Bernoulli: p^k ≥ P^k + (p - P)  (since k P^(k-1) = 1)
    have hb : (1 : ℝ) + (k : ℝ) * (p / P - 1) ≤ (1 + (p / P - 1)) ^ k :=
      one_add_mul_le_pow (by
        have : 0 ≤ p / P := by have := hp.1; positivity
        linarith) k
    have hsimp : (1 + (p / P - 1)) = p / P := by ring
    rw [hsimp, div_pow] at hb
    have hPkpos : 0 < P ^ k := pow_pos hPpos k
    have hb2 : P ^ k * (1 + K * (p / P - 1)) ≤ p ^ k := by
      have := mul_le_mul_of_nonneg_left hb hPkpos.le
      rw [mul_div_cancel₀ _ hPkpos.ne'] at this
      simpa [hKdef] using this
    -- K * P^k / P = K * P^(k-1) = 1
    have hKP : K * P ^ k / P = 1 := by
      have : P ^ k = P ^ (k - 1) * P := by
        conv_lhs => rw [show k = (k - 1) + 1 from by omega, pow_succ]
      rw [this, hPk]; field_simp
    have e2 : P ^ k * (1 + K * (p / P - 1)) = P ^ k + (p - P) * (K * P ^ k / P) := by
      field_simp <;> ring
    rw [e2, hKP] at hb2
    linarith
