-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower_bound_via_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:18:39.813745+00:00
-- url     : https://prove2.me/submissions/d1ae7a6d-d7a7-497c-bbf6-8b3ad613db23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulated_euler_count_of_maximal

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hTriangle⟩ :=
    WilliamsonShmoys.triangulated_euler_count_of_maximal K hK hCard hMax
  omega