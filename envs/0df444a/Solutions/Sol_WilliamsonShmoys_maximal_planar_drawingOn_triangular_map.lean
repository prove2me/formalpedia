-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_triangular_map
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T22:54:45.835102+00:00
-- url     : https://prove2.me/submissions/ffa67d0f-db2a-4e83-af4e-0a3f10b63091
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangular_map_exists
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangular_map_face_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    ∃ (m : Nat) (M : WilliamsonShmoys.TriangularMap H (Fin m)),
      2 * Fintype.card V = m + 4 := by
  obtain ⟨m, hM⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_triangular_map_exists H hH hV hMax
  let M : WilliamsonShmoys.TriangularMap H (Fin m) := Classical.choice hM
  exact ⟨m, M,
    WilliamsonShmoys.maximal_planar_drawing_triangular_map_face_count
      H hH hV hMax m M⟩