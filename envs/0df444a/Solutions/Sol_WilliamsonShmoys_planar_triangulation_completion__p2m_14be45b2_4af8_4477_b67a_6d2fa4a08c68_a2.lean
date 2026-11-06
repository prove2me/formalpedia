-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_14be45b2_4af8_4477_b67a_6d2fa4a08c68_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:15.855556+00:00
-- url     : https://prove2.me/submissions/3661dce0-72a9-4506-a303-d911a4a76fc5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_maximal_supergraph__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_edge_maximal_supergraph__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
      K hK hcard
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
      L hL hcard hmax⟩