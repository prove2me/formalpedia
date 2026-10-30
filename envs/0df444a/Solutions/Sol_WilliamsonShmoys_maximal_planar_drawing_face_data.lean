-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:50:05.854648+00:00
-- url     : https://prove2.me/submissions/e9a1a32c-7d05-48e2-9b9f-1c6e01e8249e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_face_data_3cb44ee4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (instF : Fintype F) (boundaryLength : F → ℕ),
      Fintype.card V + @Fintype.card F instF = H.edgeSet.ncard + 2 ∧
      (@Finset.univ F instF).sum boundaryLength = 2 * H.edgeSet.ncard ∧
      ∀ f, boundaryLength f = 3 := by
  have hE := WilliamsonShmoys.maximal_planar_drawing_edge_count_face_data_3cb44ee4
    H hDraw hMax hCard
  let m : ℕ := Fintype.card V
  let F := Fin (2 * m - 4)
  have hF : Fintype.card F = 2 * m - 4 := by
    simp [F]
  refine ⟨F, inferInstance, fun _ => 3, ?_, ?_, ?_⟩
  · change m + Fintype.card F = H.edgeSet.ncard + 2
    rw [hF, hE]
    omega
  · change (Finset.univ : Finset F).sum (fun _ => 3) = 2 * H.edgeSet.ncard
    rw [Finset.sum_const, Finset.card_univ, hF, hE]
    simp [nsmul_eq_mul]
    omega
  · intro f
    rfl