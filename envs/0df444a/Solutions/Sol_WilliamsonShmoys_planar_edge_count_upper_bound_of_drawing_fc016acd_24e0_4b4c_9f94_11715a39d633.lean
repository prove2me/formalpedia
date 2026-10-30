-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_of_drawing_fc016acd_24e0_4b4c_9f94_11715a39d633
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:07:18.609513+00:00
-- url     : https://prove2.me/submissions/dcac8cc6-c376-4553-b5a4-c9f9f19c2bec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K', hConn, hDraw', hMono⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
      K hK hCard
  have hBound :=
    WilliamsonShmoys.planar_connected_edge_bound__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
      K' hConn hDraw' hCard
  omega