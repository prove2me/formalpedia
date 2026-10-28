-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound_719d44f8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:05:13.94613+00:00
-- url     : https://prove2.me/submissions/737581fb-4389-45fb-8ab8-88cafb054e54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_euler_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hplanar, hle, hcard⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_euler_edge_count H hV hH
  calc
    H.edgeSet.ncard ≤ K.edgeSet.ncard := hle
    _ = 3 * Fintype.card V - 6 := hcard