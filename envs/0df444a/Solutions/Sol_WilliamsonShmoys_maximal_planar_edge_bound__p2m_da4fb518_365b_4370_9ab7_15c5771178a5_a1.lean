-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:06:51.86825+00:00
-- url     : https://prove2.me/submissions/8eec478a-cc31-494a-99fc-4d6238ffcd43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_embedding_counts__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
import Theorems.Thm_WilliamsonShmoys_euler_triangulation_edge_arithmetic__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    L.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  obtain ⟨F, hEuler, htri⟩ :=
    WilliamsonShmoys.maximal_planar_embedding_counts__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
      (V := V) L hcard hconn hL hmax
  exact WilliamsonShmoys.euler_triangulation_edge_arithmetic__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
    (Fintype.card V) L.edgeFinset.card F hcard hEuler htri