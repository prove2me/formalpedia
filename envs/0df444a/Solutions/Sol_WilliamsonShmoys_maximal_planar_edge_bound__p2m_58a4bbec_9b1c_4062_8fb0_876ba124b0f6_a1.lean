-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T08:49:48.135724+00:00
-- url     : https://prove2.me/submissions/3a20f6f8-c947-4fa2-8475-3d24f55c01f3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_cardinality
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      (forall u v : V, H.Adj u v -> K.Adj u v) ->
      HasPlanarDrawingOn K -> K = H)
    (hcard : 3 <= Fintype.card V) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_cardinality H hcard hH (by
      intro K hHK hK
      exact hmax K (by
        intro u v huv
        exact hHK huv) hK)
  have hcardEq : H.edgeFinset.card = H.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [hcardEq.symm] at hcount
  exact hcount