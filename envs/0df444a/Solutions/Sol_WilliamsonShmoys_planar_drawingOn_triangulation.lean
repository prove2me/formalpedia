-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T22:46:42.478659+00:00
-- url     : https://prove2.me/submissions/30908c87-08af-40e1-8296-caf6589e1237
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_triangular_map

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V), G ≤ H ∧
      ∃ (m : Nat) (M : WilliamsonShmoys.TriangularMap H (Fin m)),
        2 * Fintype.card V = m + 4 := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension G hG hV
  exact ⟨H, hGH,
    WilliamsonShmoys.maximal_planar_drawingOn_triangular_map H hH hV hMax⟩