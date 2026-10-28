-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:44:09.120231+00:00
-- url     : https://prove2.me/submissions/1e6265ca-c750-463f-bef3-398bbf45cd21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_finite_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_topological_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    Exists fun U : SimpleGraph V =>
      And (LE.le T U)
        (And (WilliamsonShmoys.HasPlanarDrawingOn U)
          (U.edgeSet.ncard = 3 * Fintype.card V - 6)) := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_extension_finite_v2 T hT
  exact ⟨U, hTU, hU,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_topological_v2 U hU hmax hV⟩
