-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_certificate_repair4_917de119
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:08.863573+00:00
-- url     : https://prove2.me/submissions/7034853d-ae90-492b-ae1b-119e68124e5d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    ∃ (F : Type) (instF : Fintype F) (boundaryLength : F → ℕ),
      (∀ f : F, 3 <= boundaryLength f) ∧
      Finset.sum (@Finset.univ F instF) boundaryLength = 2 * G.edgeSet.ncard ∧
      Fintype.card V + @Fintype.card F instF = G.edgeSet.ncard + 2 := by
  have hE : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    have := hConn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at this
    exact this
  have hU := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc G hCard hDraw
  have face_list : ∀ (e n : ℕ), n ≤ e + 1 → e + 6 ≤ 3 * n →
      ∃ m : ℕ, n + (m + 1) = e + 2 ∧ ∃ d : Fin (m + 1) → ℕ, (∑ i, d i) = 2 * e ∧ ∀ i, 3 ≤ d i := by
    intro e n h1 h2
    refine ⟨e + 1 - n, by omega, Fin.cons (2 * e - 3 * (e + 1 - n)) (fun _ => 3), ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]; omega
      · simp only [Fin.cons_succ]; omega
  obtain ⟨m, hm, d, hd, h3⟩ := face_list _ _ hE (by omega)
  exact ⟨Fin (m + 1), inferInstance, d, h3, hd, by simpa only [Fintype.card_fin] using hm⟩
