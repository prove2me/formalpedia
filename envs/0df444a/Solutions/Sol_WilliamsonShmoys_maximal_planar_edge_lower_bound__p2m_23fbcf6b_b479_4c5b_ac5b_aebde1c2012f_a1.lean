-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_23fbcf6b_b479_4c5b_ac5b_aebde1c2012f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:12:02.219269+00:00
-- url     : https://prove2.me/submissions/2baf78c9-cce3-4784-af02-b40c23350ccf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, N <= K -> HasPlanarDrawingOn K -> K = N)
    (hcard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= N.edgeFinset.card + 6 := by
  letI : DecidableRel N.Adj := dN
  have hmax' : forall K : SimpleGraph V, N <= K ->
      HasPlanarDrawingOn K -> K <= N := by
    intro K hNK hK
    exact le_of_eq (hmax K hNK hK)
  have hbound :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
      N hcard hN hmax'
  have hcount : N.edgeSet.ncard = N.edgeFinset.card := by
    classical
    simpa [SimpleGraph.edgeFinset] using
      (Set.ncard_eq_toFinset_card N.edgeSet (Set.toFinite N.edgeSet))
  rw [hcount] at hbound
  exact hbound