-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_triangulation_extension_for_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:04:57.115663+00:00
-- url     : https://prove2.me/submissions/41a71402-0ef4-41d4-9c4c-ddc3a97a0fac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_count_v2_0463fea4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_triangulation_extension_v2_0463fea4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      Set.Subset Q.edgeSet R.edgeSet ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨R, hR, hQR, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_v2_0463fea4 Q hQ
  exact ⟨R, hR, hQR,
    WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulation_extension_v2_0463fea4 R hCard hR hmax⟩