-- Prove2me | solution 1 for Zeta9Note.irrational_of_two_small_integer_forms
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T08:24:05.780583+00:00
-- url     : https://prove2.me/submissions/4ebdf8ab-55ae-4479-ae17-11ec5f0a4652

-- Public-mission submission for Zeta9Note.irrational_of_two_small_integer_forms.
-- Statement and proof verified in formalization/Zeta9Note.lean (exit 0, no placeholder).

import Mathlib

theorem solution (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b₁ a₁ b₂ a₂ : ℤ,
        b₁ * a₂ ≠ b₂ * a₁ ∧
        |(b₁ : ℝ) + (a₁ : ℝ) * x| < ε ∧
        |(b₂ : ℝ) + (a₂ : ℝ) * x| < ε) :
    Irrational x := by
  apply (irrational_iff_ne_rational x).2
  intro a b hb hx
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hbabs : 0 < |(b : ℝ)| := abs_pos.mpr hbR
  have heps : 0 < (1 : ℝ) / |(b : ℝ)| := one_div_pos.mpr hbabs
  obtain ⟨b₁, a₁, b₂, a₂, hdet, hsmall₁, hsmall₂⟩ := h _ heps
  rw [hx] at hsmall₁ hsmall₂
  have small_form_zero (c d : ℤ)
      (hs : |(c : ℝ) + (d : ℝ) * ((a : ℝ) / (b : ℝ))| <
        (1 : ℝ) / |(b : ℝ)|) : c * b + d * a = 0 := by
    have hform : (c : ℝ) + (d : ℝ) * ((a : ℝ) / (b : ℝ)) =
        ((c * b + d * a : ℤ) : ℝ) / (b : ℝ) := by
      push_cast
      field_simp
    rw [hform, abs_div] at hs
    have hreal : |((c * b + d * a : ℤ) : ℝ)| < 1 :=
      (div_lt_div_iff_of_pos_right hbabs).mp hs
    have hint : |c * b + d * a| < (1 : ℤ) := by exact_mod_cast hreal
    exact Int.abs_lt_one_iff.mp hint
  have hk₁ : b₁ * b + a₁ * a = 0 := small_form_zero b₁ a₁ hsmall₁
  have hk₂ : b₂ * b + a₂ * a = 0 := small_form_zero b₂ a₂ hsmall₂
  have hcross : (b₁ * a₂ - b₂ * a₁) * b = 0 := by
    calc
      _ = (b₁ * b + a₁ * a) * a₂ - (b₂ * b + a₂ * a) * a₁ := by ring
      _ = 0 := by rw [hk₁, hk₂]; ring
  exact hdet (sub_eq_zero.mp ((mul_eq_zero.mp hcross).resolve_right hb))
