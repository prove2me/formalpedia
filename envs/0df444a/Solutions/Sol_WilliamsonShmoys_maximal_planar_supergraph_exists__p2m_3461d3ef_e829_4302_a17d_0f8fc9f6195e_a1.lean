-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:10.475808+00:00
-- url     : https://prove2.me/submissions/9afa85cf-dda2-4bbd-bd82-d60c8a83a563

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_supergraph_maximal__p2m_233ed0bd_e0d7_41b1_8c05_73fad0336759_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    exists J : SimpleGraph V,
      And (HasPlanarDrawingOn J)
        (And (H <= J)
          (forall K : SimpleGraph V,
            HasPlanarDrawingOn K -> J <= K -> K <= J)) := by
  exact WilliamsonShmoys.finite_simpleGraph_supergraph_maximal__p2m_233ed0bd_e0d7_41b1_8c05_73fad0336759_a1
    H HasPlanarDrawingOn hH