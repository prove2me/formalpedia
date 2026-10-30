-- Prove2me | solution 1 for ZhangTangLabelCut.LP2.choose_exponents
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:08:30.404114+00:00
-- url     : https://prove2.me/submissions/0a41edb3-0db8-4ae8-b50d-ec91aea74552

import Mathlib
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

set_option autoImplicit false

namespace ZhangTangLabelCut.LP2

lemma ce_main (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 3) (k : ℕ) (hk : 2 ≤ k) :
    (50 : ℝ) ^ (-(1 / 3 - ε)) * k *
      (analyticVertices k (1 / (6 * ε) + 1 - 1 / 2) (1 / (6 * ε) + 1)) ^ (1 / 3 - ε) ≤
      (k : ℝ) ^ (1 + (1 / (6 * ε) + 1)) := by
  set δ : ℝ := 1 / (6 * ε) + 1 with hδ
  set β : ℝ := δ - 1 / 2 with hβ
  set γ : ℝ := 1 / 3 - ε with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hβ0 : 0 ≤ β := by
    rw [hβ, hδ]
    have : 0 < 1 / (6 * ε) := by positivity
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0 : ℝ) < k := by linarith
  set E : ℝ := 2 * δ + β + 2 with hE
  have hA : 1 ≤ (k : ℝ) ^ (2 * δ) := Real.one_le_rpow hk1 (by linarith)
  have hB : 1 ≤ (k : ℝ) ^ β := Real.one_le_rpow hk1 hβ0
  have hprod : (k : ℝ) ^ (2 * δ) * (k : ℝ) ^ β * (k : ℝ) ^ 2 = (k : ℝ) ^ E := by
    rw [hE, Real.rpow_add hkpos, Real.rpow_add hkpos]
    norm_cast
  have hK2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  have hV : analyticVertices k β δ ≤ 50 * (k : ℝ) ^ E := by
    unfold analyticVertices
    rw [← hprod]
    have h1 : (k : ℝ) * ((k : ℝ) - 1) / 2 ≤ (k : ℝ) ^ 2 / 2 := by nlinarith
    have h2 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity
    have h3 : (3 * (32 * (k : ℝ) ^ (2 * δ)) - 1) * (k : ℝ) ^ β ≤ 96 * (k : ℝ) ^ (2 * δ) * (k : ℝ) ^ β := by
      nlinarith
    have h4 : (0 : ℝ) ≤ (3 * (32 * (k : ℝ) ^ (2 * δ)) - 1) * (k : ℝ) ^ β := by
      apply mul_nonneg <;> linarith
    have h5 : (3 * (32 * (k : ℝ) ^ (2 * δ)) - 1) * (k : ℝ) ^ β * ((k : ℝ) * ((k : ℝ) - 1) / 2) ≤
        (96 * (k : ℝ) ^ (2 * δ) * (k : ℝ) ^ β) * ((k : ℝ) ^ 2 / 2) :=
      mul_le_mul h3 h1 h2 (by positivity)
    have h6 : (1 : ℝ) ≤ (k : ℝ) ^ (2 * δ) * (k : ℝ) ^ β * (k : ℝ) ^ 2 := by
      have := mul_le_mul hA hB (by norm_num) (by linarith)
      nlinarith
    nlinarith
  have hVpos : 0 < analyticVertices k β δ := by
    unfold analyticVertices
    have h2 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity
    have h4 : (0 : ℝ) ≤ (3 * (32 * (k : ℝ) ^ (2 * δ)) - 1) * (k : ℝ) ^ β := by
      apply mul_nonneg <;> linarith
    have := mul_nonneg h4 h2
    linarith
  have hVγ : (analyticVertices k β δ) ^ γ ≤ (50 : ℝ) ^ γ * (k : ℝ) ^ (E * γ) := by
    calc (analyticVertices k β δ) ^ γ ≤ (50 * (k : ℝ) ^ E) ^ γ :=
          Real.rpow_le_rpow hVpos.le hV hγ0.le
      _ = (50 : ℝ) ^ γ * (k : ℝ) ^ (E * γ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hkpos.le]
  have hEγ : E * γ ≤ δ := by
    have e : E * γ = δ - 9 * ε / 2 := by
      rw [hE, hβ, hγ, hδ]
      field_simp
      ring
    rw [e]; linarith
  have hk2 : (k : ℝ) ^ (E * γ) ≤ (k : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hk1 hEγ
  have h50 : (50 : ℝ) ^ (-γ) * (50 : ℝ) ^ γ = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h50p : (0 : ℝ) < (50 : ℝ) ^ (-γ) := by positivity
  rw [Real.rpow_add hkpos, Real.rpow_one]
  calc (50 : ℝ) ^ (-γ) * k * (analyticVertices k β δ) ^ γ
      ≤ (50 : ℝ) ^ (-γ) * k * ((50 : ℝ) ^ γ * (k : ℝ) ^ (E * γ)) := by
        apply mul_le_mul_of_nonneg_left hVγ (by positivity)
    _ = (k : ℝ) * (k : ℝ) ^ (E * γ) := by
        have : (50 : ℝ) ^ (-γ) * k * ((50 : ℝ) ^ γ * (k : ℝ) ^ (E * γ)) =
            ((50 : ℝ) ^ (-γ) * (50 : ℝ) ^ γ) * ((k : ℝ) * (k : ℝ) ^ (E * γ)) := by ring
        rw [this, h50, one_mul]
    _ ≤ (k : ℝ) * (k : ℝ) ^ δ := mul_le_mul_of_nonneg_left hk2 hkpos.le

theorem choose_exponents_aux (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 3) :
    ∃ δ β : ℝ, 0 < δ ∧ 0 < β ∧ δ - 1 < β ∧
      ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
        ∀ k : ℕ, k₀ ≤ k →
          C * k * (analyticVertices k β δ) ^ (1 / 3 - ε) ≤ (k : ℝ) ^ (1 + δ) := by
  have hδ0 : 0 < 1 / (6 * ε) := by positivity
  refine ⟨1 / (6 * ε) + 1, 1 / (6 * ε) + 1 - 1 / 2, by linarith, by linarith, by linarith,
    (50 : ℝ) ^ (-(1 / 3 - ε)), by positivity, 2, le_refl _, ?_⟩
  intro k hk
  exact ce_main ε hε hε' k hk

end ZhangTangLabelCut.LP2

theorem solution (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 3) :
    ∃ δ β : ℝ, 0 < δ ∧ 0 < β ∧ δ - 1 < β ∧
      ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
        ∀ k : ℕ, k₀ ≤ k →
          C * k * (ZhangTangLabelCut.LP2.analyticVertices k β δ) ^ (1 / 3 - ε) ≤ (k : ℝ) ^ (1 + δ) :=
  ZhangTangLabelCut.LP2.choose_exponents_aux ε hε hε'
