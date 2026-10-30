-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_42afe04b_4ecc_4d48_9c38_07e79025e31e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:35:41.760045+00:00
-- url     : https://prove2.me/submissions/54b3d3e3-b092-445c-9642-b17f6bdc22af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHplanar, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1
      K hK hV
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1
      H hHplanar hmax hV
  exact ⟨H, hKH, hHplanar, hcount⟩