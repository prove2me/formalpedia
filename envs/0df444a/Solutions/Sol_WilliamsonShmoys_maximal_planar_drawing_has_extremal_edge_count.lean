-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_extremal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:34:55.980781+00:00
-- url     : https://prove2.me/submissions/7183eaf4-02f3-4900-828b-98c55ba71399
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_extremal_supergraph_a67a2052

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hmax : forall Y : SimpleGraph V, HasPlanarDrawingOn Y ->
      (forall u v, X.Adj u v -> Y.Adj u v) ->
      forall u v, Y.Adj u v -> X.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    X.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hExt := WilliamsonShmoys.planar_drawing_has_extremal_supergraph_a67a2052 X hX hCard
  cases hExt with
  | intro Y hParts =>
    cases hParts with
    | intro hY hRest =>
      cases hRest with
      | intro hXY hYCard =>
        have hYX : forall u v, Y.Adj u v -> X.Adj u v := hmax Y hY hXY
        have hEq : X = Y := by
          ext u v
          exact Iff.intro (hXY u v) (hYX u v)
        simpa [hEq] using hYCard
