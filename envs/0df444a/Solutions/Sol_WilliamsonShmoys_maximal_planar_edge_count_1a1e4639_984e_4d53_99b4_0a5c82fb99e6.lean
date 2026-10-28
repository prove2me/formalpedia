-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:25:56.459831+00:00
-- url     : https://prove2.me/submissions/0243aaef-dc78-4076-822a-7d627179f957
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_drawing

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_edge_count_of_drawing K hV hK