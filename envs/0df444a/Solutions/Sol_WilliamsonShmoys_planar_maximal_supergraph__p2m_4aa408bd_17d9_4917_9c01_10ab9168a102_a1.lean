-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:22:14.086556+00:00
-- url     : https://prove2.me/submissions/830dadd3-4e66-41c1-8c60-c0a2af565534

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_graph_with_property__p2m_30b6c010_ab73_46dd_b2c7_d549b3a8cd09_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    Exists fun T : SimpleGraph V =>
      And (G.edgeSet ⊆ T.edgeSet)
        (And (HasPlanarDrawingOn T)
          (∀ H : SimpleGraph V,
            T.edgeSet ⊆ H.edgeSet →
            HasPlanarDrawingOn H →
            H.edgeSet ⊆ T.edgeSet)) := by
  exact WilliamsonShmoys.exists_maximal_graph_with_property__p2m_30b6c010_ab73_46dd_b2c7_d549b3a8cd09_a1
    (P := HasPlanarDrawingOn) G hG
