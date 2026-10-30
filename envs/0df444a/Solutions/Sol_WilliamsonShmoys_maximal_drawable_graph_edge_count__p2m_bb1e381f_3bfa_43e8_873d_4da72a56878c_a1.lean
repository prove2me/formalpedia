-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_bb1e381f_3bfa_43e8_873d_4da72a56878c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:44:01.555216+00:00
-- url     : https://prove2.me/submissions/de60fe36-3121-478f-b666-908233d99a7b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1 L hL hCard
  · exact WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1 L hL hMax hCard