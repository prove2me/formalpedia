-- Prove2me | solution 1 for TensorNP.Rank.lemma_8_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:46:42.612107+00:00
-- url     : https://prove2.me/submissions/4f5ecbfd-3810-45b4-95cd-39c8aa263a15

import Definitions.Def_TensorNP_Rank_Construction
import Theorems.Thm_TensorNP_Rank_system30_consequences
import Mathlib

open TensorNP.Rank

theorem solution :
    ¬ ∃ a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ : ℚ,
      System30 a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ := by
  rintro ⟨a₁, a₂, a₃, b₁, b₂, b₃, c₁, c₂, c₃, d₁, d₂, d₃, h⟩
  obtain ⟨hs, hn⟩ := system30_consequences a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ h
  have hd : d₂ ≠ 0 := by intro hd; simp [hd] at hn
  have hc : c₂ ≠ 0 := by
    intro hc
    have : d₂ ^ 2 = 0 := by simpa [hc] using hs.symm
    exact hd (by nlinarith)
  have hsq : (d₂ / c₂) * (d₂ / c₂) = (2 : ℚ) := by
    field_simp
    nlinarith [hs]
  have hirr : ¬ IsSquare (2 : ℚ) :=
    (irrational_sqrt_ratCast_iff_of_nonneg (q := 2) (by norm_num)).mp
      (by simpa using irrational_sqrt_two)
  exact hirr ⟨d₂ / c₂, hsq.symm⟩
