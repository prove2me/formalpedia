-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_exists__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:18:04.413605+00:00
-- url     : https://prove2.me/submissions/4622ca8f-4655-4379-9890-225da9f9ba45

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_13d6333d_8327_4de0_a7db_2786f76107ad_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) :
    Exists fun R : SimpleGraph V => And (Set.Subset Q.edgeSet R.edgeSet)
      (And (HasPlanarDrawingOn R)
        (forall S : SimpleGraph V, Set.Subset R.edgeSet S.edgeSet ->
          HasPlanarDrawingOn S -> Set.Subset S.edgeSet R.edgeSet)) := by
  exact WilliamsonShmoys.finite_maximal_supergraph__p2m_13d6333d_8327_4de0_a7db_2786f76107ad_a1
    Q HasPlanarDrawingOn hDraw