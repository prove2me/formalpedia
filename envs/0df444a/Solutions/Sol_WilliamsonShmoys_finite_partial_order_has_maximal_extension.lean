-- Prove2me | solution 1 for WilliamsonShmoys.finite_partial_order_has_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:03:24.41064+00:00
-- url     : https://prove2.me/submissions/675597db-36a7-4b7c-bc53-aa579626b265

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (R : α → Prop)
    (a : α)
    (ha : R a) :
    ∃ b : α, a ≤ b ∧ R b ∧
      ∀ c : α, b ≤ c → R c → c = b := by
  classical
  let S : Finset α := Finset.univ.filter fun x => a ≤ x ∧ R x
  have haS : a ∈ S := by
    simp [S, ha]
  let f : α → Nat := fun x => (S.filter fun y => x ≤ y).card
  obtain ⟨b, hbS, hmin⟩ := S.exists_min_image f ⟨a, haS⟩
  refine ⟨b, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hbS).2.1
  · exact (Finset.mem_filter.mp hbS).2.2
  · intro c hbc hRc
    by_contra hcb
    have hlt : b < c := lt_of_le_of_ne hbc (Ne.symm hcb)
    have hcS : c ∈ S := by
      change c ∈ Finset.univ.filter (fun x => a ≤ x ∧ R x)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_trans (Finset.mem_filter.mp hbS).2.1 hbc, hRc⟩
    have hsub : S.filter (fun y => c ≤ y) ⊂ S.filter (fun y => b ≤ y) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, le_trans hbc hy.2⟩
      · intro heq
        have hbmem : b ∈ S.filter (fun y => b ≤ y) :=
          Finset.mem_filter.mpr ⟨hbS, le_rfl⟩
        have hbmem' : b ∈ S.filter (fun y => c ≤ y) := heq.symm ▸ hbmem
        exact (not_le_of_gt hlt) (Finset.mem_filter.mp hbmem').2
    have hcard : (S.filter (fun y => c ≤ y)).card <
        (S.filter (fun y => b ≤ y)).card := Finset.card_lt_card hsub
    exact (not_lt_of_ge (hmin c hcS)) (by simpa [f] using hcard)