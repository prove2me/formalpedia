-- Prove2me | solution 1 for WilliamsonShmoys.aggregate_piece_edge_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:26:01.920342+00:00
-- url     : https://prove2.me/submissions/8e7903fa-01e1-457c-91a2-e091f919e4f4

import Mathlib

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (C : Finset (Finset V)) (e : Finset V → Nat)
    (hV : 3 ≤ Fintype.card V)
    (hcard : (∑ S ∈ C, S.card) = Fintype.card V)
    (hne : ∀ S, S ∈ C → 0 < S.card)
    (hsmall : ∀ S, S ∈ C → 0 < S.card → S.card < 3 → e S + 3 ≤ 3 * S.card)
    (hlarge : ∀ S, S ∈ C → 3 ≤ S.card → e S + 6 ≤ 3 * S.card) :
    (∑ S ∈ C, e S) + 6 ≤ 3 * (∑ S ∈ C, S.card) := by
  let margin : Finset V → Nat := fun S => if 3 ≤ S.card then 6 else 3
  have hlocal : ∀ S, S ∈ C → e S + margin S ≤ 3 * S.card := by
    intro S hS
    by_cases hlargeS : 3 ≤ S.card
    · simpa [margin, hlargeS] using hlarge S hS hlargeS
    · have hpos := hne S hS
      have hlt : S.card < 3 := by omega
      simpa [margin, hlargeS] using hsmall S hS hpos hlt
  have hsum0 := Finset.sum_le_sum (s := C) (fun S hS => hlocal S hS)
  rw [Finset.sum_add_distrib] at hsum0
  have hsum : (∑ S ∈ C, e S) + (∑ S ∈ C, margin S) ≤
      3 * (∑ S ∈ C, S.card) := by
    calc
      (∑ S ∈ C, e S) + (∑ S ∈ C, margin S) ≤ ∑ S ∈ C, 3 * S.card := hsum0
      _ = 3 * (∑ S ∈ C, S.card) := by simp [← Finset.mul_sum]
  have hmargin : 6 ≤ ∑ S ∈ C, margin S := by
    by_cases hex : ∃ S, S ∈ C ∧ 3 ≤ S.card
    · obtain ⟨S, hS, hSlarge⟩ := hex
      have hnonneg : ∀ T ∈ C, 0 ≤ margin T := by
        intro T hT
        exact Nat.zero_le _
      have hsingle := Finset.single_le_sum (s := C) hnonneg hS
      simpa [margin, hSlarge] using hsingle
    · have hnotlarge : ∀ S, S ∈ C → ¬ 3 ≤ S.card := by
        intro S hS hlargeS
        exact hex ⟨S, hS, hlargeS⟩
      have hcardle : (∑ S ∈ C, S.card) ≤ 2 * C.card := by
        calc
          (∑ S ∈ C, S.card) ≤ ∑ S ∈ C, 2 := by
            apply Finset.sum_le_sum
            intro S hS
            have hn := hnotlarge S hS
            omega
          _ = 2 * C.card := by simp [mul_comm]
      have hC : 2 ≤ C.card := by
        rw [← hcard] at hV
        omega
      have hmarginEq : (∑ S ∈ C, margin S) = 3 * C.card := by
        calc
          (∑ S ∈ C, margin S) = ∑ S ∈ C, 3 := by
            apply Finset.sum_congr rfl
            intro S hS
            have hn := hnotlarge S hS
            simp [margin, hn]
          _ = 3 * C.card := by simp [mul_comm]
      rw [hmarginEq]
      omega
  omega