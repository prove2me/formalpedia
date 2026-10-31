-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:47:39.906983+00:00
-- url     : https://prove2.me/submissions/ef82ec2b-1b0b-4cc8-aa89-1a6701364831
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  have hExt :=
    WilliamsonShmoys.planar_drawable_maximal_extension__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
      G hG
  let H := Classical.choose hExt
  have hSpec := Classical.choose_spec hExt
  have hGH : G <= H := hSpec.1
  have hH : WilliamsonShmoys.HasPlanarDrawingOn H := hSpec.2.1
  have hEdges : G.edgeSet.ncard <= H.edgeSet.ncard := hSpec.2.2.1
  have hMax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H := hSpec.2.2.2
  have hCount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
      H hCard hH hMax
  rw [hCount] at hEdges
  exact hEdges