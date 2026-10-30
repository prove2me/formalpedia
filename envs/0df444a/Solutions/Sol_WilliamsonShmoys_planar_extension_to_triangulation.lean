-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_to_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:20:53.032992+00:00
-- url     : https://prove2.me/submissions/9522759c-fe16-44cd-a559-fd6e57032ef0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_edge_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V,
      L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
      3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_extension_to_edge_maximal_supergraph L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.edge_maximal_planar_graph_edge_bound M hV hM hmax⟩