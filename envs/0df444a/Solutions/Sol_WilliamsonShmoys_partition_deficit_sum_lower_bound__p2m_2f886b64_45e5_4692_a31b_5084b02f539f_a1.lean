-- Prove2me | solution 1 for WilliamsonShmoys.partition_deficit_sum_lower_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:28:12.445766+00:00
-- url     : https://prove2.me/submissions/6f057dd9-7da7-459d-a265-2e983024210b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (parts : Finset (Finset V))
    (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C)
    (hnonempty : ∀ C, C ∈ parts → C.Nonempty)
    (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D)
    (hcard : 3 ≤ Fintype.card V) :
    6 ≤ ∑ C ∈ parts,
      (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
       else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3) := by
  classical
  let f : Finset V → Nat := fun C =>
    if 3 ≤ C.card then 6 else if C.card = 2 then 5 else 3
  have hcard_sub (C : Finset V) : Fintype.card {x : V // x ∈ C} = C.card := by
    simp
  have hsum_eq :
      (∑ C ∈ parts,
        (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
         else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3)) =
        ∑ C ∈ parts, f C := by
    apply Finset.sum_congr rfl
    intro C hC
    simp [f, hcard_sub]
  have hf : ∀ C ∈ parts, 3 ≤ f C := by
    intro C hC
    simp only [f]
    split_ifs <;> omega
  by_cases hlarge : ∃ C, C ∈ parts ∧ 3 ≤ C.card
  · obtain ⟨C, hC, hCcard⟩ := hlarge
    have hval : f C = 6 := by simp [f, hCcard]
    rw [hsum_eq]
    calc
      6 = f C := hval.symm
      _ ≤ ∑ D ∈ parts, f D :=
        Finset.single_le_sum (fun D hD => Nat.zero_le (f D)) hC
  · have hsmall : ∀ C, C ∈ parts → C.card ≤ 2 := by
      intro C hC
      have hnot : ¬ 3 ≤ C.card := fun h => hlarge ⟨C, hC, h⟩
      omega
    have hVpos : 0 < (Finset.univ : Finset V).card := by
      have : 0 < Fintype.card V := lt_of_lt_of_le (by norm_num : 0 < 3) hcard
      simpa using this
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
    obtain ⟨C, hC, hvC⟩ := hcover v
    have hCsmall := hsmall C hC
    have hout : ∃ x, x ∉ C := by
      by_contra hall
      push_neg at hall
      have hsub : (Finset.univ : Finset V) ⊆ C := by
        intro x hx
        exact hall x
      have hle := Finset.card_le_card hsub
      have hcardle : Fintype.card V ≤ C.card := by simpa using hle
      omega
    obtain ⟨x, hxC⟩ := hout
    obtain ⟨D, hD, hxD⟩ := hcover x
    have hCD : C ≠ D := by
      intro hEq
      subst D
      exact hxC hxD
    let pair : Finset (Finset V) := insert C (insert D ∅)
    have hpair : pair ⊆ parts := by
      intro E hE
      simp [pair] at hE
      rcases hE with rfl | rfl
      · exact hC
      · exact hD
    have hparts : 2 ≤ parts.card := by
      have hpaircard : pair.card = 2 := by simp [pair, hCD]
      rw [← hpaircard]
      exact Finset.card_le_card hpair
    have hsum : 3 * parts.card ≤ ∑ C ∈ parts, f C := by
      have hconstant : 3 * parts.card = ∑ C ∈ parts, (3 : Nat) := by
        simp [Nat.mul_comm]
      rw [hconstant]
      apply Finset.sum_le_sum
      intro C hC
      exact hf C hC
    rw [hsum_eq]
    omega