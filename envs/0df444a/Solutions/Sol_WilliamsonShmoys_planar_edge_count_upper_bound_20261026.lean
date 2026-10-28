-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:01:59.530743+00:00
-- url     : https://prove2.me/submissions/da9006c0-b187-4916-b6be-e7e0fe0d36eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlaneEulerData
import Theorems.Thm_WilliamsonShmoys_exists_plane_euler_data_supergraph_of_drawing
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_plane_euler_data

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨K, hJK, hData⟩ :=
    WilliamsonShmoys.exists_plane_euler_data_supergraph_of_drawing J hJ hV
  have hK := WilliamsonShmoys.edge_bound_of_plane_euler_data K hData hV
  exact (Set.ncard_mono hJK).trans hK