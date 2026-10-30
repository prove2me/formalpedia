-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_map_face_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:18:47.90182+00:00
-- url     : https://prove2.me/submissions/6f8ae57c-1e58-4e19-8bc1-1303e3540637

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangular_map_face_count

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (m : Nat)
    (M : WilliamsonShmoys.TriangularMap H (Fin m)) :
    2 * Fintype.card V = m + 4 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_triangular_map_face_count
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_triangular_map_face_count <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_triangular_map_face_count <;> assumption)
