-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:46:11.855052+00:00
-- url     : https://prove2.me/submissions/d7a7a519-24cd-497e-916d-9ed787929dcd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_finite_graph_maximal_extension__p2m_0d55c294_ea6d_4f9f_a448_4b66814798e5_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, HasPlanarDrawingOn J → H ≤ J → J = H) ∧
      G.edgeFinset.card ≤ H.edgeFinset.card := by
  exact finite_graph_maximal_extension__p2m_0d55c294_ea6d_4f9f_a448_4b66814798e5_a1
    G HasPlanarDrawingOn hG