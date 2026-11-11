-- Prove2me | solution 1 for WilliamsonShmoys.partition_allowance_sum_large_family__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T17:30:12.255608+00:00
-- url     : https://prove2.me/submissions/0ee79c82-9668-4393-8e4d-3549301b9ac6

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- For a partition of a set of size `≥ 3` into at least two nonempty parts, the sum of the
per-part allowances (`0` for a singleton, `1` for a pair, `3m-6` for `m ≥ 3`) is at most
`3n - 6`. -/
theorem solution {V : Type*} [Fintype V] (parts : Finset (Finset V))
    (hnonempty : ∀ s ∈ parts, s.Nonempty) (hparts : 2 ≤ parts.card)
    (hsum : (∑ s ∈ parts, s.card) = Fintype.card V) (hcard : 3 ≤ Fintype.card V) :
    (let f : Finset V → Nat := fun s =>
        if Fintype.card s ≤ 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6
     ∑ s ∈ parts, f s ≤ 3 * Fintype.card V - 6) := by
  dsimp only
  have hsum' : (∑ s ∈ parts, Fintype.card ↥s) = Fintype.card V := by
    simpa only [Fintype.card_coe] using hsum
  have hterm : ∀ s ∈ parts,
      (if Fintype.card ↥s ≤ 1 then 0 else if Fintype.card ↥s = 2 then 1 else 3 * Fintype.card ↥s - 6)
        ≤ 3 * Fintype.card ↥s - 3 := by
    intro s hs
    have hpos : 0 < Fintype.card ↥s := by
      rw [Fintype.card_coe]
      exact Finset.card_pos.mpr (hnonempty s hs)
    by_cases h1 : Fintype.card ↥s ≤ 1
    · rw [if_pos h1]
      omega
    · rw [if_neg h1]
      by_cases h2 : Fintype.card ↥s = 2
      · rw [if_pos h2]
        omega
      · rw [if_neg h2]
        omega
  have hsum_le : (∑ s ∈ parts,
        (if Fintype.card ↥s ≤ 1 then 0 else if Fintype.card ↥s = 2 then 1 else 3 * Fintype.card ↥s - 6)) ≤
      ∑ s ∈ parts, (3 * Fintype.card ↥s - 3) := Finset.sum_le_sum hterm
  have hdist : (∑ s ∈ parts, (3 * Fintype.card ↥s - 3)) = 3 * Fintype.card V - 3 * parts.card := by
    rw [Finset.sum_tsub_distrib]
    · rw [← Finset.mul_sum, hsum', Finset.sum_const, Nat.nsmul_eq_mul]
      omega
    · intro s hs
      have hpos : 0 < Fintype.card ↥s := by
        rw [Fintype.card_coe]
        exact Finset.card_pos.mpr (hnonempty s hs)
      omega
  have hfin : 3 * Fintype.card V - 3 * parts.card ≤ 3 * Fintype.card V - 6 :=
    Nat.sub_le_sub_left (by omega) _
  omega
