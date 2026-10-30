-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_edge_bound_cda78d6a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:23:49.711346+00:00
-- url     : https://prove2.me/submissions/09359de8-7b88-42b2-bfb9-8dd0d976135e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDrawing : HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMDrawing, hEdges⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
      L hDrawing hCard
  have hML : M = L := hMax M hLM hMDrawing
  rw [hML] at hEdges
  omega