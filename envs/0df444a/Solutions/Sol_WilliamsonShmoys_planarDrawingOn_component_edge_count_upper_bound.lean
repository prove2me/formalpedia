-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_component_edge_count_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:58:25.333917+00:00
-- url     : https://prove2.me/submissions/3680d80b-2b92-4f4b-9c28-2d2318fb583d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_component_induced_connected_and_planar_drawing_for_component_edge_bound
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound_for_component_edge_bound

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (c : M.ConnectedComponent)
    [Fintype {v : V // M.connectedComponentMk v = c}] :
    let S : Type := {v : V // M.connectedComponentMk v = c}
    let H : SimpleGraph S := M.induce (fun v => M.connectedComponentMk v = c)
    3 ≤ Fintype.card S → H.edgeSet.ncard ≤ 3 * Fintype.card S - 6 := by
  let S : Type := {v : V // M.connectedComponentMk v = c}
  let H : SimpleGraph S := M.induce (fun v => M.connectedComponentMk v = c)
  change 3 ≤ Fintype.card S → H.edgeSet.ncard ≤ 3 * Fintype.card S - 6
  intro hcard
  have hstruct :=
    WilliamsonShmoys.component_induced_connected_and_planar_drawing_for_component_edge_bound
      M hM c
  change H.Connected ∧ HasPlanarDrawingOn H at hstruct
  exact WilliamsonShmoys.connected_planar_edge_count_upper_bound_for_component_edge_bound
    H hstruct.2 hstruct.1 hcard