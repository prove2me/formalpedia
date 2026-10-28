-- Prove2me | solution 1 for WilliamsonShmoys.aggregate_connected_piece_slack
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:34:12.81037+00:00
-- url     : https://prove2.me/submissions/224d545e-f20d-453c-a969-2860ed759ed4

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (C : Finset (Finset V))
    (hCard : 3 <= Fintype.card V)
    (hCardSum : ∑ S ∈ C, S.card = Fintype.card V)
    (hEdgeSum : (L.edgeSet.ncard : Int) =
      ∑ S ∈ C, ((L.induce S).edgeSet.ncard : Int))
    (hPiece : ∀ S ∈ C,
      (((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 3) ∧
        (3 <= S.card -> ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6)) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  rw [hEdgeSum]
  have hcs : (∑ S ∈ C, (S.card : Int)) = (Fintype.card V : Int) := by exact_mod_cast hCardSum
  rcases Nat.lt_or_ge C.card 2 with h | h
  · interval_cases hc : C.card
    · rw [Finset.card_eq_zero] at hc; subst hc; simp at hCardSum; omega
    · obtain ⟨S, rfl⟩ := Finset.card_eq_one.mp hc
      simp only [Finset.sum_singleton] at hCardSum ⊢
      have := (hPiece S (by simp)).2 (by omega)
      rw [hCardSum] at this; exact this
  · calc ∑ S ∈ C, ((L.induce S).edgeSet.ncard : Int)
        ≤ ∑ S ∈ C, (3 * (S.card : Int) - 3) := Finset.sum_le_sum fun S hS => (hPiece S hS).1
      _ = 3 * (Fintype.card V : Int) - 3 * C.card := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcs]; simp; ring
      _ ≤ 3 * (Fintype.card V : Int) - 6 := by
        have : (2 : Int) ≤ C.card := by exact_mod_cast h
        omega
