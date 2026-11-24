-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_face_count__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:07.025151+00:00
-- url     : https://prove2.me/submissions/89a131a4-0370-4199-ab80-2b7653c3b52b

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
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 <= Fintype.card V) :
    exists (F : Type) (_ : Fintype F),
      Fintype.card V + Fintype.card F = M.edgeSet.ncard + 2 /\
      3 * Fintype.card F <= 2 * M.edgeSet.ncard := by
  have hE : Fintype.card V ≤ M.edgeSet.ncard + 1 := by
    have := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at this
    exact this
  have hU := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc M hV hM
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
  exact ⟨Fin (Fintype.card V + 0 + (M.edgeSet.ncard + 1 - Fintype.card V) - Fintype.card V + 1), inferInstance, by simp only [Fintype.card_fin]; omega, by simp only [Fintype.card_fin]; omega⟩
