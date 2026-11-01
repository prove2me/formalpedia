-- Prove2me | solution 2 for WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:17:36.397941+00:00
-- url     : https://prove2.me/submissions/4a36e9cb-61ee-4048-a638-202756a84827

import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H :=
  WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3 G hG
