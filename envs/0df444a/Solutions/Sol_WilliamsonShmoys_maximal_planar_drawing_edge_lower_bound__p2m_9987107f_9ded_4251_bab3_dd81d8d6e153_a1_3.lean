-- Prove2me | solution 3 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:56:16.294769+00:00
-- url     : https://prove2.me/submissions/07ddc5ff-92c7-4c3a-8189-1bd1867bfb28

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, N <= K -> HasPlanarDrawingOn K -> K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     3 * Fintype.card V <= N.edgeFinset.card + 6) := by
  exact WilliamsonShmoys.planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1 N hN hV hmax