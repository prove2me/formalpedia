-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:21:55.230194+00:00
-- url     : https://prove2.me/submissions/7ada0f7c-9b83-4ab1-8417-1abd7d078e15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj
     K.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hupper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1 K hK hcard
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1 K hK hmax hcard
  omega