-- Prove2me | solution 1 for ShapeMoment.LogConcave.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:40:27.093301+00:00
-- url     : https://prove2.me/submissions/58c320c1-301f-4989-a98a-1f50edd5cfb1

import Mathlib

set_option autoImplicit false

open Set

theorem hull_compact (n : ℕ) (S : Set (Fin n → ℝ)) (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  have key : convexHull ℝ S = ⋃ k ∈ Finset.range (n + 2),
      (fun p : (Fin k → ℝ) × (Fin k → (Fin n → ℝ)) => ∑ i, p.1 i • p.2 i) ''
        (stdSimplex ℝ (Fin k) ×ˢ Set.pi univ (fun _ => S)) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨ι, hι, z, w, hzS, hai, hw0, hw1, hwx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      have hcard : Fintype.card ι ≤ n + 1 := by
        have h1 := hai.card_le_finrank_succ
        have h2 := Submodule.finrank_le (vectorSpan ℝ (range z))
        simp only [Module.finrank_fin_fun] at h2
        omega
      let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
      simp only [mem_iUnion, mem_image, mem_prod, mem_pi, mem_univ, true_implies,
        Finset.mem_range, exists_prop]
      refine ⟨Fintype.card ι, by omega, (fun j => w (e.symm j), fun j => z (e.symm j)),
        ⟨⟨fun j => (hw0 _).le, ?_⟩, fun j => hzS ⟨_, rfl⟩⟩, ?_⟩
      · rw [Equiv.sum_comp e.symm w]; exact hw1
      · simp only
        rw [Equiv.sum_comp e.symm (fun i => w i • z i)]; exact hwx
    · intro x hx
      simp only [mem_iUnion, mem_image, mem_prod, mem_pi, mem_univ, true_implies,
        Finset.mem_range, exists_prop] at hx
      obtain ⟨k, -, ⟨w, p⟩, ⟨hw, hp⟩, rfl⟩ := hx
      exact (convex_convexHull ℝ S).sum_mem (fun i _ => hw.1 i) hw.2
        (fun i _ => subset_convexHull ℝ S (hp i))
  rw [key]
  refine (Finset.range (n + 2)).finite_toSet.isCompact_biUnion fun k _ => ?_
  refine IsCompact.image ?_ ?_
  · exact IsCompact.prod (isCompact_stdSimplex ℝ (Fin k)) (isCompact_univ_pi fun _ => hS)
  · fun_prop

theorem solution (n : ℕ) (S : Set (Fin n → ℝ)) (hS : IsCompact S) :
    IsCompact (closedConvexHull ℝ S) ∧ Convex ℝ (closedConvexHull ℝ S) := by
  have hcomp : IsCompact (convexHull ℝ S) := hull_compact n S hS
  have hc : closedConvexHull ℝ S = convexHull ℝ S := by
    rw [closedConvexHull_eq_closure_convexHull]
    exact hcomp.isClosed.closure_eq
  rw [hc]
  exact ⟨hcomp, convex_convexHull ℝ S⟩
