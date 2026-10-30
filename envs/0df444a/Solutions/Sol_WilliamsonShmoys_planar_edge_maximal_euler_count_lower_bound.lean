-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_euler_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:14:42.289546+00:00
-- url     : https://prove2.me/submissions/87d01a40-7699-4e92-a159-d87fbc54c96d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_same_vertex_euler_completion

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      M.edgeSet ⊆ N.edgeSet → N.edgeSet ⊆ M.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hN, hMN, hcount⟩ :=
    WilliamsonShmoys.planar_drawingOn_same_vertex_euler_completion M hM hV
  have hNM : N.edgeSet ⊆ M.edgeSet := hmax N hN hMN
  have hEdges : N.edgeSet = M.edgeSet := Set.Subset.antisymm hNM hMN
  have hNcard : N.edgeSet.ncard = M.edgeSet.ncard := congrArg Set.ncard hEdges
  rw [hNcard] at hcount
  exact le_of_eq hcount