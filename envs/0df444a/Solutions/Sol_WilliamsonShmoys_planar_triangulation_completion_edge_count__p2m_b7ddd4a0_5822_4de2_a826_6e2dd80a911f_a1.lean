-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_b7ddd4a0_5822_4de2_a826_6e2dd80a911f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:23:35.68431+00:00
-- url     : https://prove2.me/submissions/86f8446a-7500-4ccc-bd4c-3481f1acf5f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_supergraph__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.edge_maximal_planar_supergraph__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
      G hCard hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
      K hCard hK hmax⟩