-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_4f9da5bc_ae01_4349_bf9c_64dbf4d60dbc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:25:35.909044+00:00
-- url     : https://prove2.me/submissions/46c0f852-fb13-4ab6-93df-fcc80d3b3348

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      T ≤ U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hU, hTU, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
      T hT
  exact ⟨U, hU, hTU,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
      U hU hCard hmax⟩