-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:42:33.33611+00:00
-- url     : https://prove2.me/submissions/e0a9585d-bed1-4e88-af6c-c4eb63546721

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hQ : HasPlanarDrawingOn Q)
    (hmax : forall R : SimpleGraph V,
      (forall {u v : V}, Q.Adj u v -> R.Adj u v) ->
      HasPlanarDrawingOn R ->
      R = Q) :
    letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
    3 * Fintype.card V <= Q.edgeFinset.card + 6 := by
  classical
  letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
      Q hcard hQ (by
        intro R hQR hR
        exact hmax R (by
          intro u v huv
          exact hQR huv) hR)
  have hEdges : Q.edgeFinset.card = Q.edgeSet.ncard := by
    calc
      Q.edgeFinset.card = (Q.edgeFinset : Set (Sym2 V)).ncard :=
        (Set.ncard_coe_finset Q.edgeFinset).symm
      _ = Q.edgeSet.ncard := by rw [SimpleGraph.coe_edgeFinset]
  simpa [hEdges] using hbound