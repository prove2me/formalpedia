-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:05:34.027847+00:00
-- url     : https://prove2.me/submissions/4cec670f-76b5-481d-a694-dc74f7322baa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_drawing_edge_upper_bound H hH hV
  · obtain ⟨K, hHK, hK, hKcard⟩ :=
      WilliamsonShmoys.planar_drawing_has_triangulated_supergraph H hH hV
    have hKH : K ≤ H := hMax K hHK hK
    have hEq : K = H := le_antisymm hKH hHK
    have hcard := congrArg (fun G : SimpleGraph V => G.edgeSet.ncard) hEq
    rw [hcard] at hKcard
    exact Nat.le_of_eq hKcard.symm