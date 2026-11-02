-- Prove2me | solution 1 for SpatialDemandEq.Optimal.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:35:13.337095+00:00
-- url     : https://prove2.me/submissions/093a9e12-3750-4a98-a0c3-8789740f2192

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Theorems.Thm_SpatialDemandEq_Optimal_theorem_5
import Theorems.Thm_SpatialDemandEq_Optimal_rate_gap_identity
import Theorems.Thm_SpatialDemandEq_Optimal_eq_iff_weights
import Theorems.Thm_SpatialDemandEq_Optimal_theorem_2

open MeasureTheory
open SpatialDemandEq.Optimal

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam B : ℝ) (hS : Standing S ν dst xs c lam) (hB : lam < B)
    (μ : Fin K → ℝ) (A : Fin K → Set (E n))
    (hopt : IsLocalOpt ν S (distFn dst xs) c lam B μ A)
    (hpos : ∀ k, 0 < area ν (A k)) :
    (∃ A' : Fin K → Set (E n), IsDecentralizedEq ν S (distFn dst xs) c lam μ A') ∧
      ∀ A' : Fin K → Set (E n), IsDecentralizedEq ν S (distFn dst xs) c lam μ A' →
        ∀ k, ν (symmDiff (A' k) (A k)) = 0 := by
  obtain ⟨hcell, hμ⟩ := theorem_5 S ν dst xs c lam B hS hB μ A hopt hpos
  obtain ⟨⟨_, hsum, hstab⟩, _⟩ := hopt
  set w := optWeights c lam B (areas ν A) with hw
  have hcap : lam < ∑ k, μ k := by rw [hsum]; exact hB
  -- areas of the Voronoi cells equal the areas of `A`
  have harea : ∀ k, area ν (cell S (distFn dst xs) w k) = area ν (A k) := by
    intro k
    unfold area
    rw [measure_congr (hcell k)]
  -- the weights `w` satisfy the equilibrium condition (3) under `μ = μ**`
  have hwk : ∀ k, w k = c / (μ k - lam * area ν (A k)) := by
    intro k
    have h1 := rate_gap_identity lam B hB (areas ν A) hpos k
    have hμk : μ k = optRates lam B (areas ν A) k := by rw [hμ]
    rw [hμk]
    change w k = c / (optRates lam B (areas ν A) k - lam * areas ν A k)
    rw [div_eq_mul_one_div c, h1, hw, optWeights]
    ring
  have hEW : IsEqWeight ν S (distFn dst xs) c lam μ w := by
    intro k
    rw [harea k]
    exact ⟨hstab k, hwk k⟩
  have hEq := eq_iff_weights S ν dst xs c lam hS μ hcap
  refine ⟨⟨_, hEq.2 w hEW⟩, ?_⟩
  intro A' hA' k
  obtain ⟨hEW', hcell'⟩ := hEq.1 A' hA'
  have hww := theorem_2 S ν dst xs c lam hS μ hcap _ _ hEW' hEW
  have h3 : A' k =ᵐ[ν] A k := by
    have := hcell' k
    rw [hww] at this
    exact this.trans (hcell k).symm
  exact measure_symmDiff_eq_zero_iff.mpr h3
