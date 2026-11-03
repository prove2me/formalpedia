-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:17:39.496284+00:00
-- url     : https://prove2.me/submissions/b38bbf93-626f-44b6-9b01-730356032106

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_drawable_graph_has_maximal_drawable_extension__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       3 * Fintype.card V ≤ K.edgeFinset.card + 6) := by
  classical
  obtain ⟨K, hK, hHK, hmax⟩ :=
    drawable_graph_has_maximal_drawable_extension__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1 H hH
  have hm : ∀ N : SimpleGraph V,
      (∀ u v, K.Adj u v → N.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      ∀ u v, N.Adj u v → K.Adj u v := by
    intro N hKN hN u v huv
    exact (hmax N hN hKN) huv
  have hb := WilliamsonShmoys.maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3 K hcard hK hm
  refine ⟨K, hHK, hK, ?_⟩
  omega
