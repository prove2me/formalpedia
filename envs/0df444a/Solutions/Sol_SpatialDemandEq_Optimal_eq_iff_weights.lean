-- Prove2me | solution 1 for SpatialDemandEq.Optimal.eq_iff_weights
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:38:14.97984+00:00
-- url     : https://prove2.me/submissions/42b2b058-9cd9-4515-b1ea-cf58f9ec5da3

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Theorems.Thm_SpatialDemandEq_Optimal_cells_partition

open MeasureTheory
open SpatialDemandEq.Optimal

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ)
    (hcap : lam < ∑ k, μ k) :
    (∀ A : Fin K → Set (E n), IsDecentralizedEq ν S (distFn dst xs) c lam μ A →
        IsEqWeight ν S (distFn dst xs) c lam μ (fun i => c / (μ i - lam * area ν (A i))) ∧
          ∀ k, A k =ᵐ[ν] cell S (distFn dst xs) (fun i => c / (μ i - lam * area ν (A i))) k) ∧
      ∀ w : Fin K → ℝ, IsEqWeight ν S (distFn dst xs) c lam μ w →
        IsDecentralizedEq ν S (distFn dst xs) c lam μ (cell S (distFn dst xs) w) := by
  constructor
  · intro A hA
    obtain ⟨⟨_, hAsub, hAunion, _⟩, hstab, hpref⟩ := hA
    set w : Fin K → ℝ := fun i => c / (μ i - lam * area ν (A i)) with hw
    obtain ⟨⟨_, _, _, hnull⟩, _⟩ := cells_partition S ν dst xs c lam hS w
    have hsubcell : ∀ k, A k ⊆ cell S (distFn dst xs) w k := by
      intro k x hx
      exact ⟨hAsub k hx, fun j hj => hpref k x hx j hj⟩
    have hdiff : ∀ k, ν (cell S (distFn dst xs) w k \ A k) = 0 := by
      intro k
      have hsub : cell S (distFn dst xs) w k \ A k ⊆
          ⋃ j, ⋃ (_ : j ≠ k), (cell S (distFn dst xs) w j ∩ cell S (distFn dst xs) w k) := by
        rintro x ⟨hxc, hxA⟩
        have hxS : x ∈ (⋃ j, A j) := by rw [hAunion]; exact hxc.1
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxS
        have hjk : j ≠ k := by rintro rfl; exact hxA hj
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjk, hsubcell j hj, hxc⟩⟩
      apply measure_mono_null hsub
      exact measure_iUnion_null fun j => measure_iUnion_null fun hjk => hnull j k hjk
    have hae : ∀ k, A k =ᵐ[ν] cell S (distFn dst xs) w k := by
      intro k
      exact (hsubcell k).eventuallyLE.antisymm (ae_le_set.mpr (hdiff k))
    refine ⟨?_, hae⟩
    intro k
    have harea : area ν (cell S (distFn dst xs) w k) = area ν (A k) := by
      unfold area; rw [measure_congr (hae k)]
    rw [harea]
    exact ⟨hstab k, rfl⟩
  · intro w hw
    obtain ⟨hpart, _⟩ := cells_partition S ν dst xs c lam hS w
    refine ⟨hpart, fun k => (hw k).1, ?_⟩
    intro k x hx j hj
    rw [← (hw k).2, ← (hw j).2]
    exact hx.2 j hj
