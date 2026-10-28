-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:33:14.04226+00:00
-- url     : https://prove2.me/submissions/3b2e3018-3f66-4466-b56c-32b9d7f03153
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_d107398d
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_d107398d

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    exists H : SimpleGraph V,
      K <= H /\
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hExist := WilliamsonShmoys.maximal_planar_supergraph_d107398d K hDraw
  cases hExist with
  | intro H hRest =>
      refine Exists.intro H ?_
      refine And.intro hRest.left ?_
      refine And.intro hRest.right.left ?_
      exact WilliamsonShmoys.maximal_planar_edge_count_d107398d
        H hRest.right.left hCard hRest.right.right