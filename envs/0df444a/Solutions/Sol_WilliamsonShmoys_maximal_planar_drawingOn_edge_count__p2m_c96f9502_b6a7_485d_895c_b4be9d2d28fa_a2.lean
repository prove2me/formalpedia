-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T08:09:12.978904+00:00
-- url     : https://prove2.me/submissions/135fab46-5d5e-4791-9a07-ae1a59d57f45

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hEqMax :
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
    intro L hKL hL
    exact le_antisymm (hmax L hKL hL) hKL
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
      K hK hcard hEqMax
  have hfinset : K.edgeFinset.card = K.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card]
    exact Set.fintypeCard_eq_ncard K.edgeSet
  simpa only [← hfinset] using hcount
