-- Prove2me | solution 1 for ProphetMatchingEFGT.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:57:26.244226+00:00
-- url     : https://prove2.me/submissions/ddca1b77-99bf-4bd0-89c4-d5eae101491d

import Mathlib

theorem solution {ι : Type*} [Fintype ι] (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (a b : ι → ℝ)
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hab : ∀ s, a s + b s ≤ 1) (hsa : ∑ s, a s ≤ 1)
    (hsb : ∑ s, b s ≤ 1) :
    1 - 2 * c + c ^ 2 / 2 * ((1 - 2 * c) / (1 - c)) ^ 2 ≤
      1 - c * (∑ s, a s + ∑ s, b s) +
        c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 * ((∑ s, a s) * (∑ s, b s) - ∑ s, a s * b s) := by
  have hP : ∑ s, a s * b s ≤ (∑ s, a s + ∑ s, b s) / 4 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro s _
    have h1 := ha s
    have h2 := hb s
    have h3 := hab s
    nlinarith [sq_nonneg (a s - b s)]
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ s, a s := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ s, b s := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P, P = ∑ s, a s * b s := ⟨_, rfl⟩
  rw [← hA] at hP hsa ⊢
  rw [← hB] at hP hsb ⊢
  rw [← hPd] at hP ⊢
  have h1c : 0 < 1 - c := by linarith
  obtain ⟨r, hr⟩ : ∃ r, r = (1 - 2 * c) / (1 - c) := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 ≤ r := by rw [hr]; exact div_nonneg (by linarith) h1c.le
  have hr1 : r ≤ 1 := by rw [hr, div_le_one h1c]; linarith
  obtain ⟨K, hK⟩ : ∃ K, K = c ^ 2 * r ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hKc : K ≤ c ^ 2 := by
    rw [hK]
    have : r ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg c]
  have hcK : 0 ≤ c - 3 * K / 4 := by nlinarith
  have hu : 0 ≤ 1 - A := by linarith
  have hv : 0 ≤ 1 - B := by linarith
  have hKP := mul_le_mul_of_nonneg_left hP hK0
  have e1 := mul_nonneg hcK (add_nonneg hu hv)
  have e2 := mul_nonneg (mul_nonneg hK0 hu) hv
  rw [show c ^ 2 / 2 * r ^ 2 = K / 2 by rw [hK]; ring, show c ^ 2 * r ^ 2 = K by rw [hK]]
  nlinarith
