-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_has_euler_face_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:47:25.876434+00:00
-- url     : https://prove2.me/submissions/e33b2f4e-73c5-4205-826f-1d4fa53471b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_for_euler_certificate

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    Exists fun f : Nat =>
      K.edgeSet.ncard + 2 = Fintype.card V + f /\
        2 * K.edgeSet.ncard <= 3 * f := by
  have hedge : 3 * Fintype.card V <= K.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_bound_for_euler_certificate K hV hK hmax
  let f : Nat := K.edgeSet.ncard + 2 - Fintype.card V
  refine Exists.intro f ?_
  constructor
  · dsimp [f]
    omega
  · dsimp [f]
    omega