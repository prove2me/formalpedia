-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:10:40.863806+00:00
-- url     : https://prove2.me/submissions/567be6b1-4e22-4eb1-8040-34dad0910f06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_extend_planar_drawing_connected_42ccc764_2657_424e_8d6b_03a01aecd866
import Theorems.Thm_WilliamsonShmoys_edge_count_le_of_connected_planar_drawing_42ccc764_2657_424e_8d6b_03a01aecd866

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 <= Fintype.card V) :
    Z.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hSub, hConn, hDraw, hEdges⟩ :=
    WilliamsonShmoys.extend_planar_drawing_connected_42ccc764_2657_424e_8d6b_03a01aecd866
      Z hV hZ
  exact hEdges.trans
    (WilliamsonShmoys.edge_count_le_of_connected_planar_drawing_42ccc764_2657_424e_8d6b_03a01aecd866
      H hV hDraw hConn)