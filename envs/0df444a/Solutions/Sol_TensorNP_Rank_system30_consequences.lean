-- Prove2me | solution 1 for TensorNP.Rank.system30_consequences
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:35:31.10844+00:00
-- url     : https://prove2.me/submissions/6ebd62a9-22f5-4c7c-a9c9-6664976e6561

import Definitions.Def_TensorNP_Rank_Construction
import Mathlib

open TensorNP.Rank

theorem solution {K : Type*} [Field K] [CharZero K]
    (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ : K)
    (h : System30 a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃) :
    2 * c₂ ^ 2 - d₂ ^ 2 = 0 ∧ c₁ * d₂ * d₃ + 2 = 0 := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have u1 : a₁ * a₂ * a₃ = 2 - c₁ * c₂ * c₃ := by linear_combination h1
  have u2 : a₁ * a₃ * b₂ = -(c₁ * c₃ * d₂) := by linear_combination h2
  have u3 : a₂ * a₃ * b₁ = -(c₂ * c₃ * d₁) := by linear_combination h3
  have u4 : a₃ * b₁ * b₂ = -4 - c₃ * d₁ * d₂ := by linear_combination h4
  have u5 : a₁ * a₂ * b₃ = -(c₁ * c₂ * d₃) := by linear_combination h5
  have u6 : a₁ * b₂ * b₃ = -4 - c₁ * d₂ * d₃ := by linear_combination h6
  have u7 : a₂ * b₁ * b₃ = 4 - c₂ * d₃ * d₁ := by linear_combination h7
  have u8 : b₁ * b₂ * b₃ = -(d₁ * d₂ * d₃) := by linear_combination h8
  have m1 : (2 - c₁*c₂*c₃) * (-4 - c₁*d₂*d₃) -
      (-(c₁*c₂*d₃)) * (-(c₁*c₃*d₂)) = 0 := by
    rw [← u1, ← u6, ← u5, ← u2]
    ring
  have m2 : (2 - c₁*c₂*c₃) * (4 - c₂*d₃*d₁) -
      (-(c₁*c₂*d₃)) * (-(c₂*c₃*d₁)) = 0 := by
    rw [← u1, ← u7, ← u5, ← u3]
    ring
  have m3 : (2 - c₁*c₂*c₃) * (-4 - c₃*d₁*d₂) -
      (-(c₁*c₃*d₂)) * (-(c₂*c₃*d₁)) = 0 := by
    rw [← u1, ← u4, ← u2, ← u3]
    ring
  have m4 : (-(c₁*c₂*d₃)) * (-(d₁*d₂*d₃)) -
      (-4 - c₁*d₂*d₃) * (4 - c₂*d₃*d₁) = 0 := by
    rw [← u5, ← u8, ← u6, ← u7]
    ring
  have r1 : 2 * (c₁*c₂*c₃) - c₁*d₂*d₃ = 4 := by linear_combination m1 / 2
  have r2 : 2 * (c₁*c₂*c₃) + c₂*d₃*d₁ = 4 := by linear_combination -m2 / 2
  have r3 : 2 * (c₁*c₂*c₃) - c₃*d₁*d₂ = 4 := by linear_combination m3 / 2
  have r4 : c₂*d₃*d₁ - c₁*d₂*d₃ = 4 := by linear_combination -m4 / 4
  have ha : c₁*c₂*c₃ = 1 := by linear_combination (r1 + r2 - r4) / 4
  have hd : c₁*d₂*d₃ = -2 := by linear_combination 2 * ha - r1
  have hf : c₂*d₃*d₁ = 2 := by linear_combination r2 - 2 * ha
  have hg : c₃*d₁*d₂ = -2 := by linear_combination 2 * ha - r3
  constructor
  · have hid : (c₁*d₂*d₃) * (c₃*d₁*d₂) * c₂^2 =
        (c₁*c₂*c₃) * (c₂*d₃*d₁) * d₂^2 := by ring
    rw [ha, hd, hf, hg] at hid
    linear_combination hid / 2
  · linear_combination hd
