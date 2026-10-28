-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_count_395ae7cf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:51:14.047511+00:00
-- url     : https://prove2.me/submissions/fd01cceb-f9f5-4457-adec-5c9235f57c82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound_213a5b3a
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_strict_extension_below_triangulation_bound_213a5b3a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ J : SimpleGraph V, G ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_simple_graph_edge_upper_bound_213a5b3a G hV hG
  have hLower : 3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by
    by_contra hnot
    have hlt : G.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
    obtain ⟨J, hGJ, hne, hJ⟩ :=
      WilliamsonShmoys.planar_graph_has_strict_extension_below_triangulation_bound_213a5b3a
        G hV hG hlt
    have hEq : J = G := hmax J hGJ hJ
    exact hne hEq
  omega