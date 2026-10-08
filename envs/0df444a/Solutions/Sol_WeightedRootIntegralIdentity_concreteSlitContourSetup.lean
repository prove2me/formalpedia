-- Prove2me | solution 1 for WeightedRootIntegralIdentity.concreteSlitContourSetup
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T11:29:47.066868+00:00
-- url     : https://prove2.me/submissions/f29fcd2e-e0b1-4902-b9a0-3e6c97e76b8c

import Mathlib
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (D : Set ℂ)
    (γ : Fin 6 → ℝ → ℂ)
    (hF : DifferentiableOn ℂ
      (fun z : ℂ => ∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) D)
    (hzero : ∀ z ∈ D, z ≠ 0)
    (hpieces : ∀ j : Fin 6, ContDiffOn ℝ 1 (γ j) (Set.Icc (0 : ℝ) 1))
    (hsafe : ∀ j : Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ D) :
    DifferentiableOn ℂ
        (fun z : ℂ =>
          (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z) D ∧
      (∀ j : Fin 6, ContDiffOn ℝ 1 (γ j) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ j : Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ D) := by
  have hquot : DifferentiableOn ℂ
      (fun z : ℂ =>
        (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z) D := by
    intro z hz
    exact (hF z hz).div differentiableAt_id.differentiableWithinAt (hzero z hz)
  exact ⟨hquot, hpieces, hsafe⟩
