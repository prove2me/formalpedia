-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:23:55.863905+00:00
-- url     : https://prove2.me/submissions/01d5dd50-2f43-4e54-b414-f3f69d085fd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Exists fun L : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn L)
        (And (Set.Subset M.edgeSet L.edgeSet)
          (L.edgeSet.ncard = 3 * Fintype.card V - 6)) := by
  cases WilliamsonShmoys.planar_completion_exists_maximal_supergraph M hM with
  | intro L h =>
    cases h with
    | intro hL h =>
      cases h with
      | intro hsub hmax =>
        exact Exists.intro L
          (And.intro hL
            (And.intro hsub
              (WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count
                L hV hL hmax)))
