-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangular_map__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:45:27.483746+00:00
-- url     : https://prove2.me/submissions/3abf2295-4d9d-4c80-a1ce-d9cc8d31e7e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_data__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    ∃ (F : Type) (instF : Fintype F),
      Nonempty (@WilliamsonShmoys.TriangularMap V ‹Fintype V› H F instF) := by
  obtain ⟨F, instF, corner, dart, dart_tail, dart_head, corners_distinct,
      vertex_covered, rotation_transitive⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_data__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
      H hH hV hMax
  have hConnected : H.Connected :=
    WilliamsonShmoys.maximal_planar_drawing_connected__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
      H hH hV hMax
  exact ⟨F, instF, ⟨{
    corner := corner
    dart := dart
    dart_tail := dart_tail
    dart_head := dart_head
    corners_distinct := corners_distinct
    vertex_covered := vertex_covered
    connected := hConnected
    rotation_transitive := rotation_transitive
  }⟩⟩