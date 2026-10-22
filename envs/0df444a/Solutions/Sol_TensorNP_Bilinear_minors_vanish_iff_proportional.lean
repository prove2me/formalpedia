-- Prove2me | solution 1 for TensorNP.Bilinear.minors_vanish_iff_proportional
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:58:27.642993+00:00
-- url     : https://prove2.me/submissions/9924cdd0-048a-4231-bb27-8d5086dfe290

import Mathlib
import Definitions.Def_TensorNP_Bilinear_Construction

set_option autoImplicit false

open TensorNP.Bilinear

theorem solution {N : ℕ} (v w : Fin N → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    (∀ ab : MinorIdx N, ∑ p, ∑ q, (minorSlice ab p q : ℂ) * v p * w q = 0) ↔
      ∃ c : ℂ, v = c • w := by
  have key : ∀ ab : MinorIdx N, ∑ p, ∑ q, (minorSlice ab p q : ℂ) * v p * w q =
      v ab.1.1 * w ab.1.2 - v ab.1.2 * w ab.1.1 := by
    intro ab
    simp only [minorSlice]
    push_cast
    simp [sub_mul, Finset.sum_sub_distrib, ite_and]
  constructor
  · intro h
    have hh : ∀ a b : Fin N, v a * w b = v b * w a := by
      intro a b
      rcases lt_trichotomy a b with hab | hab | hab
      · have := h ⟨(a, b), hab⟩
        rw [key] at this
        exact sub_eq_zero.mp this
      · rw [hab]
      · have := h ⟨(b, a), hab⟩
        rw [key] at this
        exact (sub_eq_zero.mp this).symm
    obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hw (funext hcon)
    refine ⟨v b / w b, ?_⟩
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    have := hh a b
    linear_combination this
  · rintro ⟨c, rfl⟩ ab
    rw [key]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
