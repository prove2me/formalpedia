-- Prove2me | solution 1 for WittenAdSHolography.power_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:09:26.145228+00:00
-- url     : https://prove2.me/submissions/ce16a6e9-62de-491c-b8ed-c006bd6930e7

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

set_option autoImplicit false

open WittenAdSHolography MeasureTheory Filter Topology in
theorem solution (d : ℕ) (msq Δ : ℝ) (hΔ : Δ * (Δ - d) = msq) :
    IsMassiveSolution d msq (fun x₀ _ => x₀ ^ Δ) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp1 : p.1 ≠ 0 := (Set.mem_prod.mp hp).1.ne'
    exact (ContDiffAt.rpow_const_of_ne contDiffAt_fst hp1).contDiffWithinAt
  · intro x₀ hx₀ x
    have h1 : ∀ t : ℝ, deriv (fun t : ℝ => t ^ Δ) t = Δ * t ^ (Δ - 1) := fun t =>
      Real.deriv_rpow_const t Δ
    have hd0 : d0 (d := d) (fun x₀ _ => x₀ ^ Δ) = fun t _ => Δ * t ^ (Δ - 1) := by
      funext t y
      simp only [d0]
      exact h1 t
    have hdd : d0 (d0 (d := d) (fun x₀ _ => x₀ ^ Δ)) x₀ x = Δ * ((Δ - 1) * x₀ ^ (Δ - 1 - 1)) := by
      rw [hd0]
      simp only [d0]
      rw [deriv_const_mul_field']
      show Δ * deriv (fun t : ℝ => t ^ (Δ - 1)) x₀ = _
      rw [Real.deriv_rpow_const]
    have hdj : ∀ j : Fin d, dj j (dj j (fun x₀ _ => x₀ ^ Δ)) x₀ x = 0 := by
      intro j
      simp [dj]
    simp only [hypLaplacian, hdd, hdj, Finset.sum_const_zero, add_zero]
    rw [show d0 (d := d) (fun x₀ _ => x₀ ^ Δ) x₀ x = Δ * x₀ ^ (Δ - 1) from by rw [hd0]]
    have hx : x₀ ≠ 0 := hx₀.ne'
    simp only [Real.rpow_sub_one hx]
    rw [← hΔ]
    field_simp
    ring
