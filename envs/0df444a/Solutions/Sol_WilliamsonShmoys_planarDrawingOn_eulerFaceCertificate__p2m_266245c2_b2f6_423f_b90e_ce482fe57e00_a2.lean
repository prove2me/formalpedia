-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_eulerFaceCertificate__p2m_266245c2_b2f6_423f_b90e_ce482fe57e00_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:07.635402+00:00
-- url     : https://prove2.me/submissions/cfbf8511-1eaa-4b00-9d3c-eab0dabe214f

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
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (F : ℕ) (degree : Fin F → ℕ),
      Fintype.card V + F = L.edgeSet.ncard + 2 ∧
      (∑ f : Fin F, degree f) = 2 * L.edgeSet.ncard ∧
      ∀ f : Fin F, 3 ≤ degree f := by
  have hE : Fintype.card V ≤ L.edgeSet.ncard + 1 := by
    have := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at this
    exact this
  have hU := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc L hcard hL
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
  exact ⟨m + 1, d, hm, hd, h3⟩
