-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_repair_543ac5d4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:09:25.806711+00:00
-- url     : https://prove2.me/submissions/65857876-1234-4929-9912-819fea36ca93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_repair_543ac5d4
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_repair_543ac5d4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V,
      G <= U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      3 * Fintype.card V = U.edgeSet.ncard + 6 := by
  obtain ⟨U, hGU, hU, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_repair_543ac5d4 G hG
  have hcount :=
    WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4 U hV hU hmax
  exact ⟨U, hGU, hU, hcount⟩
