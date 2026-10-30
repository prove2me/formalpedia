-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_triangulation__p2m_02b7676f_a513_46e6_8e4a_f3d718372bb1_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:30.009377+00:00
-- url     : https://prove2.me/submissions/48e4e921-bf8d-49bc-b3f7-3658017f457d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_18fad212_36ea_4c15_83d2_5b7bd6c85e9a_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
        3 * f = 2 * H.edgeSet.ncard := by
  obtain ⟨J, hHJ, hJDraw, hJEdges⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_18fad212_36ea_4c15_83d2_5b7bd6c85e9a_a1
      H hDraw hV
  have hJH : J = H := hMax J hHJ hJDraw
  have hEdges : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    rw [← hJH]
    exact hJEdges
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  omega