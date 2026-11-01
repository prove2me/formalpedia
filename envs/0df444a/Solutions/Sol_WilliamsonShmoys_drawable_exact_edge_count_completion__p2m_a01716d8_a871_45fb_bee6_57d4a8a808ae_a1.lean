-- Prove2me | solution 1 for WilliamsonShmoys.drawable_exact_edge_count_completion__p2m_a01716d8_a871_45fb_bee6_57d4a8a808ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:20:55.190654+00:00
-- url     : https://prove2.me/submissions/92f5a179-8378-4f54-ae7f-6d72b87f8500

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1 G hG
  refine ⟨K, hGK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_edge_count__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1 K hcard hK hmax