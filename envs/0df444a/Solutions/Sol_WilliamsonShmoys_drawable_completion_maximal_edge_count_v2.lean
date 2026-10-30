-- Prove2me | solution 1 for WilliamsonShmoys.drawable_completion_maximal_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:34:53.495325+00:00
-- url     : https://prove2.me/submissions/a90a2b44-15f5-438e-b6ec-c519b14e4e48

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_completion_triangulation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall P : SimpleGraph V,
      (forall {u v}, N.Adj u v -> P.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn P ->
      (forall {u v}, P.Adj u v -> N.Adj u v))
    (hV : 3 <= Fintype.card V) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hcompletion :=
    WilliamsonShmoys.drawable_completion_triangulation N hdraw hV
  let P : SimpleGraph V := Classical.choose hcompletion
  have hPdata := Classical.choose_spec hcompletion
  have hNP : forall {u v}, N.Adj u v -> P.Adj u v := hPdata.1
  have hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P := hPdata.2.1
  have hPcard : P.edgeSet.ncard = 3 * Fintype.card V - 6 := hPdata.2.2
  have hPN : forall {u v}, P.Adj u v -> N.Adj u v :=
    hmax P hNP hPdraw
  have hEq : P = N := by
    ext u v
    constructor
    case mp =>
      intro huv
      exact hPN huv
    case mpr =>
      intro huv
      exact hNP huv
  simpa [hEq] using hPcard