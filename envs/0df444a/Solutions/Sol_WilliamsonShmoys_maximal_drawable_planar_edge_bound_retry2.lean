-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_planar_edge_bound_retry2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:48:14.574465+00:00
-- url     : https://prove2.me/submissions/83368776-f086-4f97-aad0-ee5c908e55f0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound_from_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKDraw, hBound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_bound_from_drawing H hDraw hCard
  have hKH : K.edgeSet ⊆ H.edgeSet := hMax K hHK hKDraw
  have hEdges : H.edgeSet = K.edgeSet := Set.Subset.antisymm hHK hKH
  have hNcard : H.edgeSet.ncard = K.edgeSet.ncard := congrArg Set.ncard hEdges
  omega