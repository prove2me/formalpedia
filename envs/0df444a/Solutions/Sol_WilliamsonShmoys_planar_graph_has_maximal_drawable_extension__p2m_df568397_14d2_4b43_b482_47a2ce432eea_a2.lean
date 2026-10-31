-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_maximal_drawable_extension__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:42:23.606022+00:00
-- url     : https://prove2.me/submissions/d9339f94-ed3b-43e1-911d-c8d1d9b37a15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
import Theorems.Thm_finite_simpleGraph_has_maximal_extension__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by
  exact finite_simpleGraph_has_maximal_extension__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
    HasPlanarDrawingOn
    (fun G H hHG hG =>
      planarDrawingOn_subgraph__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
        (G := G) (H := H) hHG hG)
    H hH