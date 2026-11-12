-- Prove2me | solution 1 for WilliamsonShmoys.sum_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T14:57:48.758839+00:00
-- url     : https://prove2.me/submissions/f5dca606-31fa-411b-adde-72d487047d05

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- Summing local edge bounds over a vertex partition yields the global planar edge bound. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V) (parts : Finset (Finset V))
    (hCardSum : (∑ s ∈ parts, Fintype.card {v // v ∈ s}) = Fintype.card V)
    (hEdgeSum : (∑ s ∈ parts, (H.induce (↑s : Set V)).edgeSet.ncard) = H.edgeSet.ncard)
    (hLocal : ∀ s ∈ parts, 1 ≤ Fintype.card {v // v ∈ s} ∧
      (H.induce (↑s : Set V)).Connected ∧
      (H.induce (↑s : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3) ≤
      3 * Fintype.card {v // v ∈ s}) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  let e : Finset V → Nat := fun s => (H.induce (↑s : Set V)).edgeSet.ncard
  let a : Finset V → Nat := fun s => if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3
  have hterm : ∀ s ∈ parts, e s + a s ≤ 3 * Fintype.card {v // v ∈ s} := by
    intro s hs
    exact (hLocal s hs).2.2
  have hsum_le : (∑ s ∈ parts, (e s + a s)) ≤
      ∑ s ∈ parts, 3 * Fintype.card {v // v ∈ s} :=
    Finset.sum_le_sum hterm
  have hsum_split : (∑ s ∈ parts, (e s + a s)) = H.edgeSet.ncard + ∑ s ∈ parts, a s := by
    rw [Finset.sum_add_distrib]
    rw [show (∑ s ∈ parts, e s) = H.edgeSet.ncard from by simpa [e] using hEdgeSum]
  have hthree : (∑ s ∈ parts, 3 * Fintype.card {v // v ∈ s}) = 3 * Fintype.card V := by
    rw [← Finset.mul_sum, hCardSum]
  have h6 : 6 ≤ ∑ s ∈ parts, a s := by
    have hne : parts.Nonempty := by
      rcases Finset.eq_empty_or_nonempty parts with rfl | h
      · simp at hCardSum
        omega
      · exact h
    have ha3 : ∀ s ∈ parts, 3 ≤ a s := by
      intro s hs
      unfold a
      split_ifs <;> omega
    rcases Nat.lt_or_ge parts.card 2 with hlt | hge
    · have hc1 : parts.card = 1 := by
        have hpos : 0 < parts.card := Finset.card_pos.mpr hne
        omega
      obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hc1
      have hc3 : 3 ≤ Fintype.card {v // v ∈ t} := by
        have hct : Fintype.card {v // v ∈ t} = Fintype.card V := by
          simpa using hCardSum
        omega
      have hat : a t = 6 := by
        unfold a
        rw [if_pos hc3]
      simp [hat]
    · have hsum3 : (∑ s ∈ parts, (3 : Nat)) ≤ ∑ s ∈ parts, a s :=
        Finset.sum_le_sum ha3
      have hconst : (∑ s ∈ parts, (3 : Nat)) = parts.card * 3 :=
        Finset.sum_const_nat (fun _ _ => rfl)
      rw [hconst] at hsum3
      have h63 : 6 ≤ parts.card * 3 := by omega
      exact h63.trans hsum3
  have hmain : H.edgeSet.ncard + ∑ s ∈ parts, a s ≤ 3 * Fintype.card V := by
    rw [← hsum_split]
    exact hsum_le.trans hthree.le
  omega
