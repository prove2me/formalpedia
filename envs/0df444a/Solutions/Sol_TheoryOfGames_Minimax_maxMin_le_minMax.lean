-- Prove2me | solution 1 for TheoryOfGames.Minimax.maxMin_le_minMax
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:24:28.502778+00:00
-- url     : https://prove2.me/submissions/fdeb9786-63fc-4250-b4bd-d5e59b863eee

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_SaddlePoint

set_option autoImplicit false

open TheoryOfGames.Minimax in
theorem solution {X Y : Type*} (φ : X → Y → ℝ) (hφ : MaxMinAttained φ) :
    maxMin φ ≤ minMax φ := by
  obtain ⟨x₀, hx₀⟩ := hφ.maxMin_attained
  obtain ⟨y₀, hy₀⟩ := hφ.minMax_attained
  have : Nonempty X := ⟨x₀⟩
  have : Nonempty Y := ⟨y₀⟩
  have h1 : maxMin φ ≤ minOver φ x₀ := by
    unfold maxMin
    exact ciSup_le hx₀
  have h4 : maxOver φ y₀ ≤ minMax φ := by
    unfold minMax
    exact le_ciInf hy₀
  have h2 : minOver φ x₀ ≤ φ x₀ y₀ := by
    obtain ⟨y₁, hy₁⟩ := hφ.min_attained x₀
    unfold minOver
    exact ciInf_le ⟨φ x₀ y₁, by rintro _ ⟨y, rfl⟩; exact hy₁ y⟩ y₀
  have h3 : φ x₀ y₀ ≤ maxOver φ y₀ := by
    obtain ⟨x₁, hx₁⟩ := hφ.max_attained y₀
    unfold maxOver
    exact le_ciSup ⟨φ x₁ y₀, by rintro _ ⟨x, rfl⟩; exact hx₁ x⟩ x₀
  linarith
