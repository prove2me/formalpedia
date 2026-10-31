-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:06.131009+00:00
-- url     : https://prove2.me/submissions/7a368cb3-469b-4b82-8626-1959890b0f4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_supergraph_of_property__p2m_aab4ced3_2cb3_4a94_814b_7026a53a954f_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V =>
      M <= N /\ WilliamsonShmoys.HasPlanarDrawingOn N /\
        (forall P : SimpleGraph V, N <= P -> WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) := by
  exact finite_maximal_supergraph_of_property__p2m_aab4ced3_2cb3_4a94_814b_7026a53a954f_a2
    M WilliamsonShmoys.HasPlanarDrawingOn hM