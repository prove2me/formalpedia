-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_via_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:55:15.201659+00:00
-- url     : https://prove2.me/submissions/69692f66-6090-402f-acc4-d1b695c24377
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_completion_exists

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hmax : forall N : SimpleGraph V,
      (forall {u v}, M.Adj u v -> N.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  classical
  let completion := WilliamsonShmoys.drawable_completion_exists M hM hV
  let N := completion.choose
  have hMN : forall {u v}, M.Adj u v -> N.Adj u v :=
    completion.choose_spec.1
  have hN : WilliamsonShmoys.HasPlanarDrawingOn N :=
    completion.choose_spec.2.1
  have hcard : N.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    completion.choose_spec.2.2
  have hNM : N = M :=
    hmax N (fun {u v} huv => hMN huv) hN
  rw [hNM] at hcard
  exact le_of_eq hcard.symm
