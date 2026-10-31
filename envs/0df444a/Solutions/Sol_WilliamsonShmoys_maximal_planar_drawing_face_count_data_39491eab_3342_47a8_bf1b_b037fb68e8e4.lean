-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_count_data_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:33:07.086885+00:00
-- url     : https://prove2.me/submissions/a6b96a6e-a23e-43c1-ad33-dd60988a48f6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_face_count_data

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    Nonempty (WilliamsonShmoys.PlanarFaceCountData K) := by
  have hE : K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_for_face_count_data K hK hV hMax
  refine ⟨2 * Fintype.card V - 4, fun _ => 3, ?_, ?_, ?_⟩
  · rw [hE]
    omega
  · simp
    rw [hE]
    omega
  · intro f
    rfl