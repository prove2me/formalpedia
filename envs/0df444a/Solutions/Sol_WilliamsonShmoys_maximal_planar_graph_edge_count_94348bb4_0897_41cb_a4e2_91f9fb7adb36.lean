-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_94348bb4_0897_41cb_a4e2_91f9fb7adb36
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:10:31.580524+00:00
-- url     : https://prove2.me/submissions/7d6165dc-fb75-4eef-bdf7-c09e492d00ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_30a2cd75
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_30a2cd75

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hmax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_30a2cd75 M hM hV
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_30a2cd75
      M hM hV hmax
  omega
