-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_b1ccffd4_b471_45dd_901d_142379850b78_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:41:13.770534+00:00
-- url     : https://prove2.me/submissions/7149b844-77ae-4128-9723-a4cc027c8aef

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

/-- The assigned target follows by taking an inclusion-maximal planar extension
and applying the edge count theorem for maximal planar graphs. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
      G hV hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
      K hV hK hmax⟩