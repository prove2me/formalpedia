-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:00:32.587733+00:00
-- url     : https://prove2.me/submissions/dbfcb82c-acc3-4128-b59f-d71fe23c4782

import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_edge_count

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn N)
    (hmax : forall H : SimpleGraph V,
      (forall u v, N.Adj u v -> H.Adj u v) ->
      HasPlanarDrawingOn H -> H = N) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    3 * Fintype.card V - 6 <= N.edgeFinset.card := by
  classical
  have hcount : N.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.finite_maximal_drawable_edge_count N hdraw hcard
      (fun T hsub hT => hmax T (fun u v hadj => @hsub u v hadj) hT)
  rw [hcount.symm]
  simpa [SimpleGraph.edgeFinset] using
    (Set.ncard_eq_toFinset_card N.edgeSet).le
