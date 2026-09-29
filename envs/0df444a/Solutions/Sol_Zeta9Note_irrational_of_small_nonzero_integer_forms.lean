-- Prove2me | solution 1 for Zeta9Note.irrational_of_small_nonzero_integer_forms
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T08:24:07.251742+00:00
-- url     : https://prove2.me/submissions/778c9c7e-bf97-42d4-966b-ffbc6db6e555

-- Public-mission submission for Zeta9Note.irrational_of_small_nonzero_integer_forms.
-- Statement and proof verified in formalization/Zeta9Note.lean (exit 0, no placeholder).

import Mathlib

theorem solution (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b a : ℤ,
        (b : ℝ) + (a : ℝ) * x ≠ 0 ∧
        |(b : ℝ) + (a : ℝ) * x| < ε) :
    Irrational x := by
  apply (irrational_iff_ne_rational x).2
  intro p q hq hx
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs : 0 < |(q : ℝ)| := abs_pos.mpr hqR
  have heps : 0 < (1 : ℝ) / |(q : ℝ)| := one_div_pos.mpr hqabs
  obtain ⟨b, a, hne, hsmall⟩ := h _ heps
  rw [hx] at hsmall hne
  have hform : (b : ℝ) + (a : ℝ) * ((p : ℝ) / (q : ℝ)) =
      ((b * q + a * p : ℤ) : ℝ) / (q : ℝ) := by
    push_cast
    field_simp
  rw [hform, abs_div] at hsmall
  have hreal : |((b * q + a * p : ℤ) : ℝ)| < 1 :=
    (div_lt_div_iff_of_pos_right hqabs).mp hsmall
  have hint : |b * q + a * p| < (1 : ℤ) := by exact_mod_cast hreal
  have hzero : b * q + a * p = 0 := Int.abs_lt_one_iff.mp hint
  have hvan : (b : ℝ) + (a : ℝ) * ((p : ℝ) / (q : ℝ)) = 0 := by
    rw [hform, hzero]
    simp
  exact hne hvan
