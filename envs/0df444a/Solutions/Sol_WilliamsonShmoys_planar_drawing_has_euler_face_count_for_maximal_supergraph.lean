-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_euler_face_count_for_maximal_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:54:20.450309+00:00
-- url     : https://prove2.me/submissions/2b5f13d1-3351-48f8-be84-b5b7b55d1533
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_extremal_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hWX : forall u v, W.Adj u v -> X.Adj u v)
    (hmax : forall Y : SimpleGraph V, HasPlanarDrawingOn Y ->
      (forall u v, W.Adj u v -> Y.Adj u v) ->
      forall u v, Y.Adj u v -> X.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    exists f : Nat,
      (Fintype.card V : Int) - (X.edgeSet.ncard : Int) + (f : Int) = 2 := by
  have hXmax : forall Y : SimpleGraph V, HasPlanarDrawingOn Y ->
      (forall u v, X.Adj u v -> Y.Adj u v) ->
      forall u v, Y.Adj u v -> X.Adj u v := by
    intro Y hY hXY u v huv
    exact hmax Y hY (fun a b hab => hXY a b (hWX a b hab)) u v huv
  have hedge := WilliamsonShmoys.maximal_planar_drawing_has_extremal_edge_count
    X hX hXmax hCard
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  omega