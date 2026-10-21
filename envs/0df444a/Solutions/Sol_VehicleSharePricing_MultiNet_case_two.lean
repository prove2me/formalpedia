-- Prove2me | solution 1 for VehicleSharePricing.MultiNet.case_two
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:16:25.208121+00:00
-- url     : https://prove2.me/submissions/e1a4bcb9-f37e-4bab-ae8a-c01c1f3774d4

import Mathlib
set_option autoImplicit false

lemma vsp_L (a y θ : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (y + θ) / (a + y + 1) ≤ (1 - θ) * (y / (a + y)) + θ * ((y + 1) / (a + y + 1)) := by
  have h1 : y / (a + y + 1) ≤ y / (a + y) := by
    rcases hy.eq_or_lt with h | h
    · rw [← h]; simp
    · exact div_le_div_of_nonneg_left hy (by linarith) (by linarith)
  have h2 : (y + θ) / (a + y + 1) = (1 - θ) * (y / (a + y + 1)) + θ * ((y + 1) / (a + y + 1)) := by
    field_simp
    ring
  rw [h2]
  have := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hθ1)
  linarith

lemma vsp_T (p1 B1 B2 K : ℝ) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ 1 - p1)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hK : 0 ≤ K) :
    K / (B1 + B2 + K) ≤ p1 * (K * p1) / (B1 + K * p1) + (1 - p1) * (K * (1 - p1)) / (B2 + K * (1 - p1)) := by
  rcases hK.eq_or_lt with h | hK'
  · rw [← h]; simp
  rcases hp1.eq_or_lt with h | hp1'
  · rw [← h]
    simp only [mul_zero, zero_mul, zero_div, zero_add, sub_zero, one_mul, mul_one]
    exact div_le_div_of_nonneg_left hK (by linarith) (by linarith)
  rcases hp2.eq_or_lt with h | hp2'
  · have : p1 = 1 := by linarith
    subst this
    simp only [mul_one, sub_self, mul_zero, zero_mul, zero_div, add_zero, one_mul]
    exact div_le_div_of_nonneg_left hK (by linarith) (by linarith)
  have hv1 : 0 < B1 + K * p1 := by positivity
  have hv2 : 0 < B2 + K * (1 - p1) := by positivity
  rw [div_add_div _ _ hv1.ne' hv2.ne', div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [mul_nonneg hK (sq_nonneg (p1 * (B2 + K * (1 - p1)) - (1 - p1) * (B1 + K * p1)))]

lemma vsp_key (p1 a1 a2 : ℝ) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ 1 - p1)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (K : ℕ) :
    ∃ K₁ K₂ : ℕ, K₁ + K₂ = K ∧
      (K : ℝ) / (a1 + a2 + 1 + K) ≤
        p1 * (K₁ : ℝ) / (a1 + K₁) + (1 - p1) * (K₂ : ℝ) / (a2 + K₂) := by
  rcases Nat.eq_zero_or_pos K with rfl | hKpos
  · exact ⟨0, 0, by simp, by simp⟩
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hp1' : p1 ≤ 1 := by linarith
  have hx0 : 0 ≤ (K : ℝ) * p1 := by positivity
  have hxK : (K : ℝ) * p1 ≤ K := by nlinarith
  set m : ℕ := ⌊(K : ℝ) * p1⌋₊ with hmdef
  have hm : (m : ℝ) ≤ K * p1 := Nat.floor_le hx0
  have hm2 : (K : ℝ) * p1 < m + 1 := Nat.lt_floor_add_one _
  have hmK : (m : ℝ) ≤ K := hm.trans hxK
  have hmK' : m ≤ K := by exact_mod_cast hmK
  by_cases hθ : (m : ℝ) = K * p1
  · -- integral case
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hmK'
    have hnr : (K : ℝ) = m + n := by exact_mod_cast hn
    refine ⟨m, n, by omega, ?_⟩
    have hn' : (n : ℝ) = K * (1 - p1) := by rw [mul_sub, mul_one, ← hθ]; linarith
    have hT := vsp_T p1 a1 a2 K hp1 hp2 ha1 ha2 hKr.le
    rw [← hθ, ← hn'] at hT
    refine le_trans ?_ hT
    exact div_le_div_of_nonneg_left hKr.le (by positivity) (by linarith)
  · have hmlt : (m : ℝ) < K * p1 := lt_of_le_of_ne hm hθ
    have hmK2 : m < K := by
      have : (m : ℝ) < K := by linarith
      exact_mod_cast this
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hmK2)
    have hnr : (K : ℝ) = m + 1 + n := by push_cast [Nat.succ_eq_add_one] at hn ⊢; exact_mod_cast hn
    obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = K * p1 - m := ⟨_, rfl⟩
    have hθ0 : 0 < θ := by linarith
    have hθ1 : θ < 1 := by linarith
    set T : ℝ := (K : ℝ) / (a1 + a2 + 1 + K) with hTdef
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    by_cases hA : T ≤ p1 * (m : ℝ) / (a1 + m) + (1 - p1) * ((n + 1 : ℕ) : ℝ) / (a2 + ((n + 1 : ℕ) : ℝ))
    · exact ⟨m, n + 1, by omega, hA⟩
    · push_neg at hA
      refine ⟨m + 1, n, by omega, ?_⟩
      by_contra hB
      push_neg at hB
      -- combination
      have hL1 := vsp_L a1 m θ ha1 hm0 hθ0.le hθ1.le
      have hL2 := vsp_L a2 n (1 - θ) ha2 hn0 (by linarith) (by linarith)
      rw [show (n : ℝ) + (1 - θ) = n + 1 - θ by ring] at hL2
      have hT := vsp_T p1 (a1 + 1 - θ) (a2 + θ) K hp1 hp2 (by linarith) (by linarith) hKr.le
      have e1 : a1 + 1 - θ + K * p1 = a1 + m + 1 := by rw [hθd]; ring
      have e2 : a2 + θ + K * (1 - p1) = a2 + n + 1 := by rw [hθd, hnr]; ring
      have e3 : a1 + 1 - θ + (a2 + θ) + K = a1 + a2 + 1 + K := by ring
      have e4 : K * p1 = m + θ := by rw [hθd]; ring
      have e5 : K * (1 - p1) = n + 1 - θ := by rw [mul_sub, mul_one, e4, hnr]; ring
      rw [e1, e2, e3, e4, e5] at hT
      have hc1 := mul_le_mul_of_nonneg_left hL1 hp1
      have hc2 := mul_le_mul_of_nonneg_left hL2 hp2
      have hid : (1 - θ) * (p1 * (m : ℝ) / (a1 + m) + (1 - p1) * ((n + 1 : ℕ) : ℝ) / (a2 + ((n + 1 : ℕ) : ℝ)))
          + θ * (p1 * ((m + 1 : ℕ) : ℝ) / (a1 + ((m + 1 : ℕ) : ℝ)) + (1 - p1) * (n : ℝ) / (a2 + n))
          = p1 * ((1 - θ) * ((m : ℝ) / (a1 + m)) + θ * (((m : ℝ) + 1) / (a1 + m + 1)))
            + (1 - p1) * ((1 - (1 - θ)) * ((n : ℝ) / (a2 + n)) + (1 - θ) * (((n : ℝ) + 1) / (a2 + n + 1))) := by
        push_cast
        ring
      have hlow : T ≤ (1 - θ) * (p1 * (m : ℝ) / (a1 + m) + (1 - p1) * ((n + 1 : ℕ) : ℝ) / (a2 + ((n + 1 : ℕ) : ℝ)))
          + θ * (p1 * ((m + 1 : ℕ) : ℝ) / (a1 + ((m + 1 : ℕ) : ℝ)) + (1 - p1) * (n : ℝ) / (a2 + n)) := by
        rw [hid]
        have h1 : p1 * (m + θ) / (a1 + m + 1) = p1 * ((m + θ) / (a1 + m + 1)) := by ring
        have h2 : (1 - p1) * (n + 1 - θ) / (a2 + n + 1) = (1 - p1) * ((n + 1 - θ) / (a2 + n + 1)) := by ring
        have hT' : T ≤ p1 * (m + θ) / (a1 + m + 1) + (1 - p1) * (n + 1 - θ) / (a2 + n + 1) := hT
        exact le_trans hT' (by
          have := add_le_add hc1 hc2
          calc _ = p1 * ((m + θ) / (a1 + m + 1)) + (1 - p1) * ((n + 1 - θ) / (a2 + n + 1)) := by rw [h1, h2]
            _ ≤ _ := this)
      nlinarith [mul_pos (sub_pos.2 hθ1) (sub_pos.2 hA), mul_pos hθ0 (sub_pos.2 hB)]

theorem solution (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp : p₁ + p₂ = 1)
    (N₁ N₂ : ℕ) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (K : ℕ) :
    ∃ K₁ K₂ : ℕ, K₁ + K₂ = K ∧
      (K : ℝ) / ((N₁ : ℝ) + (N₂ : ℝ) + (K : ℝ) - 1 + (M₁ + M₂)) ≤
        p₁ * (K₁ : ℝ) / ((N₁ : ℝ) + (K₁ : ℝ) - 1 + M₁) +
          p₂ * (K₂ : ℝ) / ((N₂ : ℝ) + (K₂ : ℝ) - 1 + M₂) := by
  have h1 : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
  have h2 : (1 : ℝ) ≤ N₂ := by exact_mod_cast hN₂
  have hp2 : p₂ = 1 - p₁ := by linarith
  subst hp2
  obtain ⟨K₁, K₂, hK, h⟩ := vsp_key p₁ ((N₁ : ℝ) - 1 + M₁) ((N₂ : ℝ) - 1 + M₂) hp₁ hp₂
    (by linarith) (by linarith) K
  refine ⟨K₁, K₂, hK, ?_⟩
  have e0 : (N₁ : ℝ) + (N₂ : ℝ) + (K : ℝ) - 1 + (M₁ + M₂) = ((N₁ : ℝ) - 1 + M₁) + ((N₂ : ℝ) - 1 + M₂) + 1 + K := by ring
  have e1 : (N₁ : ℝ) + (K₁ : ℝ) - 1 + M₁ = ((N₁ : ℝ) - 1 + M₁) + K₁ := by ring
  have e2 : (N₂ : ℝ) + (K₂ : ℝ) - 1 + M₂ = ((N₂ : ℝ) - 1 + M₂) + K₂ := by ring
  rw [e0, e1, e2]
  exact h
