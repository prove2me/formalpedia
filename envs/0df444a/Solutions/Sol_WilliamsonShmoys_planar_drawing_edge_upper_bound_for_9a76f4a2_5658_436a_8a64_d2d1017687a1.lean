-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:24:37.848628+00:00
-- url     : https://prove2.me/submissions/c7c40b86-a26d-4183-990f-a8c878fbd9c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension_6be1e368_254d_44b7_8aa7_b4001ba314b4
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_6be1e368_254d_44b7_8aa7_b4001ba314b4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hcard, hHdraw, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_extension_6be1e368_254d_44b7_8aa7_b4001ba314b4 L hdraw
  have hHcard := WilliamsonShmoys.edge_maximal_planar_edge_count_6be1e368_254d_44b7_8aa7_b4001ba314b4 H hV hHdraw hmax
  exact le_trans hcard (by rw [hHcard])