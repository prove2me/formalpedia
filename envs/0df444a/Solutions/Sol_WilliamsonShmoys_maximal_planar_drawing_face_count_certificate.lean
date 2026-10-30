-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_count_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:18:47.17827+00:00
-- url     : https://prove2.me/submissions/3b0c373f-7ab6-4246-a82e-8509e109e511

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_card

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hEdges := WilliamsonShmoys.maximal_planar_graph_edge_card L hL hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega