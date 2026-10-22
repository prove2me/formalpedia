-- Prove2me | solution 1 for RegMatroidXC.Main.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:27:42.401536+00:00
-- url     : https://prove2.me/submissions/4aa0f00b-a994-4cb1-aeb7-3586d11244c7

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a b : ℝ) (hf : ConvexOn ℝ (Set.Icc a b) f) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ b - a) :
    f (a + ε) + f (b - ε) ≤ f a + f b := by
  rcases eq_or_lt_of_le (sub_nonneg.mpr (show a ≤ b by linarith)) with h | h
  · have hab : b = a := by linarith
    have : ε = 0 := by linarith
    subst hab; subst this; simp
  set L := b - a with hL
  have hLpos : 0 < L := h
  -- a + ε = (1 - t) a + t b with t = ε / L ; b - ε = t a + (1 - t) b
  set t := ε / L with ht
  have ht0 : 0 ≤ t := div_nonneg hε₀ hLpos.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hLpos]; exact hε₁
  have hmem_a : a ∈ Set.Icc a b := ⟨le_refl _, by linarith⟩
  have hmem_b : b ∈ Set.Icc a b := ⟨by linarith, le_refl _⟩
  have e1 : (1 - t) • a + t • b = a + ε := by
    simp only [smul_eq_mul]; rw [ht]; field_simp; ring
  have e2 : t • a + (1 - t) • b = b - ε := by
    simp only [smul_eq_mul]; rw [ht]; field_simp; ring
  have h1 := hf.2 hmem_a hmem_b (sub_nonneg.mpr ht1) ht0 (by ring)
  have h2 := hf.2 hmem_a hmem_b ht0 (sub_nonneg.mpr ht1) (by ring)
  rw [e1] at h1
  rw [e2] at h2
  simp only [smul_eq_mul] at h1 h2
  nlinarith
