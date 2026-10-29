-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_retry2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:33:41.103982+00:00
-- url     : https://prove2.me/submissions/228ba7c0-1689-44b8-b9b0-bec0423ee4ca

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_retry2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_retry2
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hExt :=
    WilliamsonShmoys.planar_drawing_maximal_extension_retry2 L hL
  cases hExt with
  | intro M hRest =>
    cases hRest with
    | intro hLM hRest2 =>
      cases hRest2 with
      | intro hM hMax =>
        exact Exists.intro M (And.intro hLM
          (And.intro hM
            (WilliamsonShmoys.maximal_planar_graph_edge_count_retry2
              M hV hM hMax)))