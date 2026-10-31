-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_deff29d9_5a9a_4a55_a466_fc15c898aa4f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:34:35.645005+00:00
-- url     : https://prove2.me/submissions/c0b037e8-52b6-43e3-815e-e738b8946306
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_completion__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_exact_edge_count__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_completion__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
      H hV hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.edge_maximal_planar_graph_has_exact_edge_count__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
      K hV hK hmax⟩