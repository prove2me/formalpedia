-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:37:42.274447+00:00
-- url     : https://prove2.me/submissions/fb1ff29e-665b-4d52-a1d5-8a7d3897a743

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ H : SimpleGraph V, U ≤ H → HasPlanarDrawingOn H → H ≤ U) :
    letI : DecidableRel U.Adj := Classical.decRel U.Adj
    U.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : DecidableRel U.Adj := Classical.decRel U.Adj
  have hm : ∀ H : SimpleGraph V, U ≤ H → HasPlanarDrawingOn H → H = U := by
    intro H hUH hH
    exact le_antisymm (hmax H hUH hH) hUH
  have he := WilliamsonShmoys.maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2 U hU hm hV
  omega