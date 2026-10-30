-- Prove2me | solution 1 for WilliamsonShmoys.maximal_edge_lower_for_triangular_incidence_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:43:50.814263+00:00
-- url     : https://prove2.me/submissions/13afd940-2fc7-4136-bd75-fa801f8cf9f7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_edge_bound_f2bcadcd_42d3_4cf2_b4cc_052a8cb334d1

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
    3 * (Fintype.card V : Int) - 6 <= (X.edgeSet.ncard : Int) := by
  obtain ⟨Y, hY, hXY, hYCard⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_edge_bound_f2bcadcd_42d3_4cf2_b4cc_052a8cb334d1
      X hX hCard
  have hWY : forall u v, W.Adj u v -> Y.Adj u v := by
    intro u v huv
    exact hXY u v (hWX u v huv)
  have hYX : forall u v, Y.Adj u v -> X.Adj u v := by
    intro u v huv
    exact hmax Y hY hWY u v huv
  have hEq : X = Y := by
    ext u v
    exact ⟨hXY u v, hYX u v⟩
  rw [hEq]
  exact hYCard