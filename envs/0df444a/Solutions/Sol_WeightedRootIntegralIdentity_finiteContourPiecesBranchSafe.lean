-- Prove2me | solution 1 for WeightedRootIntegralIdentity.finiteContourPiecesBranchSafe
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:52:22.46639+00:00
-- url     : https://prove2.me/submissions/3efe9584-7170-4fde-932f-615e9e61ded3

import Mathlib

theorem solution
    (D : Set ℂ) (γ : Fin 6 → ℝ → ℂ)
    (hpieces : ∀ j : Fin 6, ContDiffOn ℝ 1 (γ j) (Set.Icc (0 : ℝ) 1))
    (hsafe : ∀ j : Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ D) :
    (∀ j : Fin 6, ContDiffOn ℝ 1 (γ j) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ j : Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ D) := by
  exact ⟨hpieces, hsafe⟩
