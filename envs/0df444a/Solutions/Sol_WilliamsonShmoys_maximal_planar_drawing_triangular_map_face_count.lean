-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangular_map_face_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:00:54.906969+00:00
-- url     : https://prove2.me/submissions/fecaec0e-28c4-42bc-88e6-e96c626b4aeb

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count
import Theorems.Thm_WilliamsonShmoys_triangular_map_face_dart_count

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
  have hEdge := WilliamsonShmoys.maximal_planar_drawing_edge_count H hH hV hMax
  have hDart := WilliamsonShmoys.triangular_map_face_dart_count H M
  omega