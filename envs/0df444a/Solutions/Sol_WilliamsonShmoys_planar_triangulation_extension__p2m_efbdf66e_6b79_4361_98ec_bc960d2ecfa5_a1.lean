-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_efbdf66e_6b79_4361_98ec_bc960d2ecfa5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:49.494624+00:00
-- url     : https://prove2.me/submissions/3e45ef84-36b6-4b10-b1de-8fb90393c6d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hPlanar, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1
      K hDraw
  exact ⟨L, hKL, hPlanar,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1
      L hPlanar hMax hV⟩