-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_retry2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:48:51.395963+00:00
-- url     : https://prove2.me/submissions/a5a03ce1-76fa-43a2-914d-1d279ac4836c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_retry2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_retry2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound_retry2 M hV hM
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound_retry2 M hV hM hMax
  omega
