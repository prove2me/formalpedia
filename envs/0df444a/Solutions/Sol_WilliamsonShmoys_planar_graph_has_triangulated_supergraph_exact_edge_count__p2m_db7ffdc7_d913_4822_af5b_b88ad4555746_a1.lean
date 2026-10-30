-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_db7ffdc7_d913_4822_af5b_b88ad4555746_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:49.433065+00:00
-- url     : https://prove2.me/submissions/850a782e-6cd4-4320-9bfb-d98d0724ec6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_supergraph__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      3 * Fintype.card V - 6 = T.edgeSet.ncard := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
      L hV hL
  refine ⟨T, hLT, hT, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
    T hV hT hmax