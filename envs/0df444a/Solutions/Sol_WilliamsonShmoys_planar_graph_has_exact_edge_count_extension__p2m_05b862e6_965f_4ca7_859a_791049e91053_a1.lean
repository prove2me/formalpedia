-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_exact_edge_count_extension__p2m_05b862e6_965f_4ca7_859a_791049e91053_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:06.018978+00:00
-- url     : https://prove2.me/submissions/bd94e7b0-407e-4a59-882b-33e858bf8c61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNDraw, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
      M hDraw hV
  exact ⟨N, hMN, hNDraw,
    WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
      N hNDraw hV hMax⟩