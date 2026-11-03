-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_census__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T07:12:28.074575+00:00
-- url     : https://prove2.me/submissions/5efd459f-3fca-4ea9-9cd1-6965bf716c81

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
import Mathlib

open scoped BigOperators
set_option autoImplicit false

private theorem list_sum_eq_fin_sum_get (l : List ℕ) :
    (∑ i : Fin l.length, l.get i) = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [Fin.sum_univ_succ, ih]

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (F : ℕ) (boundary : Fin F → ℕ),
      Fintype.card V + F = K.edgeFinset.card + 2 ∧
      (∑ f : Fin F, boundary f) = 2 * K.edgeFinset.card ∧
      ∀ f : Fin F, 3 ≤ boundary f := by
  letI : DecidableRel K.Adj := dK
  obtain ⟨f, lengths, hEuler, hlen, hsum, hbound⟩ :=
    WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
      K hK hcard hconn
  have hedge : K.edgeSet.ncard = K.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  refine ⟨lengths.length, fun i => lengths.get i, ?_, ?_, ?_⟩
  · rw [hlen]
    omega
  · change (∑ i : Fin lengths.length, lengths.get i) =
      2 * K.edgeFinset.card
    rw [list_sum_eq_fin_sum_get, hsum, hedge]
  · intro i
    exact hbound _ (List.get_mem _ _)