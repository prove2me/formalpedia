-- Prove2me | solution 1 for WilliamsonShmoys.partition_size_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:14:09.725733+00:00
-- url     : https://prove2.me/submissions/d1a4ae29-8891-47ad-942c-43ae8a48afaa

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (K : SimpleGraph V)
    (parts : Finset (Finset V))
    (hparts :
      (∀ s ∈ parts, s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) ∧
        (∀ v, ∃ s ∈ parts, v ∈ s) ∧
        (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧
        (∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s)) :
    (let f : Finset V → Nat := fun s =>
      if Fintype.card s ≤ 1 then 0 else
      if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6;
      ∑ s ∈ parts, f s ≤ 3 * Fintype.card V - 6) := by
  rcases hparts with ⟨hlocal, hcover, hdisj, _⟩
  let f : Finset V → Nat := fun s =>
    if Fintype.card s ≤ 1 then 0 else
    if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6
  have hunion : parts.biUnion (fun x => x) = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      simpa using hcover v
  have hsum : (∑ s ∈ parts, s.card) = Fintype.card V := by
    calc
      (∑ s ∈ parts, s.card) = (parts.biUnion (fun x => x)).card := by
        symm
        exact Finset.card_biUnion hdisj
      _ = Fintype.card V := by
        rw [hunion]
        simp
  have hterm (s : Finset V) (hs : s ∈ parts) : f s + 3 ≤ 3 * s.card := by
    have hp : 1 ≤ Fintype.card s := by
      have hpos : 0 < s.card := Finset.card_pos.mpr (hlocal s hs).1
      simpa using hpos
    have hsc : Fintype.card s = s.card := by simp
    dsimp [f]
    split_ifs <;> omega
  have hsumterm : (∑ s ∈ parts, (f s + 3)) ≤ ∑ s ∈ parts, (3 * s.card) := by
    apply Finset.sum_le_sum
    intro s hs
    exact hterm s hs
  have hparts_pos : 0 < parts.card := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    obtain ⟨s, hs, _⟩ := hcover v
    exact Finset.card_pos.mpr ⟨s, hs⟩
  by_cases hone : parts.card = 1
  · obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hone
    have hscard : s.card = Fintype.card V := by
      have := hsum
      simpa [hs] using this
    have hcs : 3 ≤ Fintype.card s := by
      simpa [hscard] using hcard
    rw [hs]
    simp only [Finset.sum_singleton]
    change f s ≤ 3 * Fintype.card V - 6
    have hsF : Fintype.card s = s.card := by simp
    have hlarge : 3 ≤ s.card := by omega
    dsimp [f]
    rw [hsF]
    have hgt : ¬ s.card ≤ 1 := by omega
    have hne : s.card ≠ 2 := by omega
    simp only [if_neg hgt, if_neg hne]
    omega
  · have hcount : 2 ≤ parts.card := by omega
    have hsumterm' : (∑ s ∈ parts, f s) + 3 * parts.card ≤ 3 * Fintype.card V := by
      calc
        (∑ s ∈ parts, f s) + 3 * parts.card = ∑ s ∈ parts, (f s + 3) := by
          rw [Finset.sum_add_distrib]
          simp
          omega
        _ ≤ ∑ s ∈ parts, (3 * s.card) := hsumterm
        _ = 3 * Fintype.card V := by
          rw [← Finset.mul_sum, hsum]
    change (∑ s ∈ parts, f s) ≤ 3 * Fintype.card V - 6
    omega
