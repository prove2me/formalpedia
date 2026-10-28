-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_from_drawing_20261027
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:19:44.910473+00:00
-- url     : https://prove2.me/submissions/1e28e25a-ad70-4989-8b19-d332dccc72bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_large_e9dfd49a
import Theorems.Thm_WilliamsonShmoys_connected_drawing_edge_bound_large_e9dfd49a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    (G.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨H, hGH, hH, hConnected, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_large_e9dfd49a G hG hCard
  have hUpper :=
    WilliamsonShmoys.connected_drawing_edge_bound_large_e9dfd49a H hH hConnected hCard
  exact le_trans hCount hUpper