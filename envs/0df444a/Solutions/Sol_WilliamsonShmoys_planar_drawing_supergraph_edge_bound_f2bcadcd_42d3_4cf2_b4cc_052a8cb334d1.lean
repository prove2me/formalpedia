-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_edge_bound_f2bcadcd_42d3_4cf2_b4cc_052a8cb334d1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:13:36.985253+00:00
-- url     : https://prove2.me/submissions/0221cc25-e475-4ae3-864b-f74ee42377c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_6daa1fb6
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_6daa1fb6

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    ∃ Y : SimpleGraph V, HasPlanarDrawingOn Y ∧
      (∀ u v, X.Adj u v → Y.Adj u v) ∧
      3 * (Fintype.card V : Int) - 6 <= (Y.edgeSet.ncard : Int) := by
  obtain ⟨Y, hY, hXY, hMax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_supergraph_6daa1fb6 X hX
  have hCount :=
    WilliamsonShmoys.maximal_drawable_edge_count_6daa1fb6 Y hY hMax hCard
  refine ⟨Y, hY, hXY, ?_⟩
  omega