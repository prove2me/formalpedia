-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:11:14.672501+00:00
-- url     : https://prove2.me/submissions/e326e085-777f-4184-936c-2ab7ac6db65a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq__p2m_aef21287_1e8b_49ab_be32_8e780786d8be_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M <= L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by
  letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  have heq := WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_aef21287_1e8b_49ab_be32_8e780786d8be_a1
    L hcard hconn hL hmax
  omega