-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:41:07.427107+00:00
-- url     : https://prove2.me/submissions/8a63db38-4e2f-466a-a696-bed428c395f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_d0a96286_d6d0_4f9d_8f16_8ff04549e9c7_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_d0a96286_d6d0_4f9d_8f16_8ff04549e9c7_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) H hH