-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangular_incidence_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:17:31.031984+00:00
-- url     : https://prove2.me/submissions/4eefcef2-f558-4a1d-ae77-306909662d60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_for_triangular_incidence_count
import Theorems.Thm_WilliamsonShmoys_maximal_edge_lower_for_triangular_incidence_count

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
    (hCard : 3 <= Fintype.card V)
    (f : Nat)
    (hEuler : (Fintype.card V : Int) - (X.edgeSet.ncard : Int) + (f : Int) = 2) :
    (3 : Int) * (f : Int) = 2 * (X.edgeSet.ncard : Int) := by
  have hup := WilliamsonShmoys.planar_edge_upper_for_triangular_incidence_count X hX hCard
  have hlo := WilliamsonShmoys.maximal_edge_lower_for_triangular_incidence_count
    W X hX hWX hmax hCard
  omega