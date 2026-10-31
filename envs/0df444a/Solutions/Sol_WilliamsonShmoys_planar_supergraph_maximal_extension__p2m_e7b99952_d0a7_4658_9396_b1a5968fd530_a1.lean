-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:31.798191+00:00
-- url     : https://prove2.me/submissions/52a4c040-9cfd-425b-ac69-84a87b583cc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawing_of_subgraph__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
import Theorems.Thm_exists_maximal_supergraph_of_hereditary_property__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ N : SimpleGraph V,
      K.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ M : SimpleGraph V,
        N.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = N.edgeSet := by
  obtain ⟨N, hKN, hN, hmax⟩ :=
    exists_maximal_supergraph_of_hereditary_property__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
      (fun G => WilliamsonShmoys.HasPlanarDrawingOn G) K hK
      (by
        intro G H hHG hG
        exact WilliamsonShmoys.drawing_of_subgraph__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2 H G hHG hG)
  exact ⟨N, hKN, hN, hmax⟩