-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:22.508135+00:00
-- url     : https://prove2.me/submissions/ad5def2f-931a-4a37-b0fa-2f9223987980

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_extension__p2m_1863c0cc_84bc_4e3a_b61f_07ce03271d4c_a1

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hJK, hKDraw, hKCount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_1863c0cc_84bc_4e3a_b61f_07ce03271d4c_a1
      J hDraw hV
  have hKJ : K = J := hMax K hJK hKDraw
  simpa [hKJ] using hKCount