-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound_for_supergraph_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:26:03.90046+00:00
-- url     : https://prove2.me/submissions/f7d88e52-fc9d-453a-b2ab-366ba6594218

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_supergraph_completion

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hcard⟩ :=
    WilliamsonShmoys.planar_graph_has_dense_supergraph_completion L hV hL
  have hML : M = L := hmax M hLM hM
  rw [hML] at hcard
  omega