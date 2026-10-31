-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:28:13.886494+00:00
-- url     : https://prove2.me/submissions/91438ca1-37fc-43d8-acc0-9ae794a8e19a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
      H hH
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.edge_maximal_planar_graph_edge_count__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
    K hV hK hMax