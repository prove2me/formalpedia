-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:30:36.374744+00:00
-- url     : https://prove2.me/submissions/03d157bc-e38d-4660-84b2-3264a4daef57

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_exact_edge_supergraph

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hEdges⟩ :=
    WilliamsonShmoys.planar_graph_has_exact_edge_supergraph H hH hCard
  have hEq : K = H := hMax K hHK hK
  rw [← hEq]
  exact hEdges