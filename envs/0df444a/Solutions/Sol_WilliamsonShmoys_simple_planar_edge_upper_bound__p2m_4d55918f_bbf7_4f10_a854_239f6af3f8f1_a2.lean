-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:32:59.474708+00:00
-- url     : https://prove2.me/submissions/345095a7-3d65-4108-a7ea-537b51d0ccb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawing_maximal_extension__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hCard, hMax⟩ :=
    WilliamsonShmoys.drawing_maximal_extension__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
      K hK hV
  have hCount :=
    WilliamsonShmoys.maximal_drawing_edge_count__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
      H hMax hV
  omega