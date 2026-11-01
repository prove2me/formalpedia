-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_to_triangulation__p2m_0448f4f3_6535_4d82_8dda_cbfbd113fe3f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:23:28.990136+00:00
-- url     : https://prove2.me/submissions/a0b598c3-4406-4892-b2b2-fad4291610cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨K, hGK, hK, hMax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
      G hG
  have hCount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
      K hK hcard hMax
  exact ⟨K, hGK, hK, hCount⟩