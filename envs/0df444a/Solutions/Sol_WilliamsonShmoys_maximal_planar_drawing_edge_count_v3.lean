-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:21:58.282575+00:00
-- url     : https://prove2.me/submissions/4d2e174c-af62-46a8-9eab-eb5e04daf160
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hmax : HasPlanarDrawingOn M ∧
      ∀ M' : SimpleGraph V,
        (∀ u v, M.Adj u v → M'.Adj u v) →
        HasPlanarDrawingOn M' →
        ∀ u v, M'.Adj u v → M.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hTdraw, hMT, hTcard⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangulation_extension
      M hmax.1 hCard
  have hTM : ∀ u v, T.Adj u v → M.Adj u v := hmax.2 T hMT hTdraw
  have hEq : M = T := by
    apply SimpleGraph.ext
    funext u v
    exact propext ⟨hMT u v, hTM u v⟩
  rw [hEq]
  exact hTcard