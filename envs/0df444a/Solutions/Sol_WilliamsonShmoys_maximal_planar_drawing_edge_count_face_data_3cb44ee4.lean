-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_face_data_3cb44ee4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:07:20.776624+00:00
-- url     : https://prove2.me/submissions/dc5ebc85-5e78-49f8-9927-52ece59ed818

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_face_data

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hDrawJ, hEdgesJ⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_face_data H hDraw hCard
  have hEq : J = H := hMax J hHJ hDrawJ
  rw [hEq] at hEdgesJ
  exact hEdgesJ