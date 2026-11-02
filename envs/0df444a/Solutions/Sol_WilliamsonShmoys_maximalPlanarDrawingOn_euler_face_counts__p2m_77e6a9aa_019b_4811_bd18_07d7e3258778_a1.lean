-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarDrawingOn_euler_face_counts__p2m_77e6a9aa_019b_4811_bd18_07d7e3258778_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:16:32.936821+00:00
-- url     : https://prove2.me/submissions/c22822a0-d82d-45b7-9264-d112de26a488
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edge_count__p2m_6162c346_56e0_4291_a049_fac9204b7241_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    Exists fun f : Nat =>
      2 * K.edgeSet.ncard = 3 * f /\
      Fintype.card V + f = K.edgeSet.ncard + 2 := by
  have hEdge := WilliamsonShmoys.maximalPlanarDrawingOn_edge_count__p2m_6162c346_56e0_4291_a049_fac9204b7241_a1 K hK hCard hmax
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  constructor <;> omega