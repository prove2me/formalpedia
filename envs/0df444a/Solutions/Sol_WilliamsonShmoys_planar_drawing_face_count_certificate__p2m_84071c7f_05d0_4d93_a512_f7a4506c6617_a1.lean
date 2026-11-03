-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_84071c7f_05d0_4d93_a512_f7a4506c6617_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T09:20:03.672684+00:00
-- url     : https://prove2.me/submissions/c714a4a8-08a7-4100-8351-5030ffee2d1e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_certificate_for_edge_bound_4091134b
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hConnected : K.Connected)
    (hPlanar : HasPlanarDrawingOn K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 1 ≤ Fintype.card V ∨
    ∃ (f : ℕ) (boundaryLength : Fin f → ℕ),
      Fintype.card V + f = K.edgeFinset.card + 2 ∧
      (∑ i : Fin f, boundaryLength i) = 2 * K.edgeFinset.card ∧
      ∀ i : Fin f, 3 ≤ boundaryLength i := by
  classical
  by_cases hV : 3 ≤ Fintype.card V
  · obtain ⟨lengths, hLower, hSum, hEuler⟩ :=
      WilliamsonShmoys.planar_drawing_face_boundary_certificate_for_edge_bound_4091134b
        K hPlanar hConnected hV
    let f : ℕ := lengths.length
    let boundaryLength : Fin f → ℕ :=
      fun i => lengths.get (Fin.cast (by dsimp [f]) i)
    have hEdge : K.edgeSet.ncard = K.edgeFinset.card := by
      calc
        K.edgeSet.ncard = (Set.toFinset K.edgeSet).card :=
          Set.ncard_eq_toFinset_card' K.edgeSet
        _ = Fintype.card K.edgeSet := Set.toFinset_card _
        _ = K.edgeFinset.card := SimpleGraph.edgeFinset_card.symm
    have hSumGet :
        (∑ i : Fin lengths.length, lengths.get i) = lengths.sum := by
      calc
        (∑ i : Fin lengths.length, lengths.get i) =
            (List.ofFn (fun i : Fin lengths.length => lengths.get i)).sum :=
          List.sum_ofFn.symm
        _ = lengths.sum := congrArg List.sum (List.ofFn_get lengths)
    have hSumFin : (∑ i : Fin f, boundaryLength i) = lengths.sum := by
      simpa [boundaryLength, f] using hSumGet
    have hEuler' : Fintype.card V + f = K.edgeFinset.card + 2 := by
      calc
        Fintype.card V + f = Fintype.card V + lengths.length := by rfl
        _ = K.edgeSet.ncard + 2 := hEuler
        _ = K.edgeFinset.card + 2 := congrArg (fun e : ℕ => e + 2) hEdge
    have hSum' : (∑ i : Fin f, boundaryLength i) = 2 * K.edgeFinset.card := by
      calc
        (∑ i : Fin f, boundaryLength i) = lengths.sum := hSumFin
        _ = 2 * K.edgeSet.ncard := hSum
        _ = 2 * K.edgeFinset.card := congrArg (fun e : ℕ => 2 * e) hEdge
    refine Or.inr ⟨f, boundaryLength, hEuler', hSum', ?_⟩
    intro i
    apply hLower
    exact List.get_mem _ _
  · left
    have hNonempty : Nonempty V := hConnected.nonempty
    letI := hNonempty
    have hnpos : 0 < Fintype.card V := Fintype.card_pos
    have hnlt : Fintype.card V < 3 := by omega
    have hedge : K.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
    have hcases : Fintype.card V = 1 ∨ Fintype.card V = 2 := by omega
    rcases hcases with h | h
    · rw [h] at hedge ⊢
      have hedge' : K.edgeFinset.card ≤ 0 := by simpa using hedge
      calc
        K.edgeFinset.card + 1 ≤ 0 + 1 :=
          Nat.add_le_add_right hedge' 1
        _ = 1 := by norm_num
    · rw [h] at hedge ⊢
      have hedge' : K.edgeFinset.card ≤ 1 := by simpa using hedge
      calc
        K.edgeFinset.card + 1 ≤ 1 + 1 :=
          Nat.add_le_add_right hedge' 1
        _ = 2 := by norm_num
