-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_finite_preorder__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:37:48.026452+00:00
-- url     : https://prove2.me/submissions/5c2efdba-070c-4fc0-821d-104ff24aa255

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [Preorder α] (x : α) (Q : α → Prop) (hx : Q x) : ∃ y : α, Q y ∧ x ≤ y ∧ ∀ z : α, Q z → y ≤ z → z ≤ y := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let β := {y : α // Q y ∧ x ≤ y}
  letI : Fintype β := Fintype.ofFinite β
  let s (y : α) : Finset α := Finset.univ.filter fun w => Q w ∧ w ≤ y
  let score (a : β) : Nat := (s a.1).card
  have hnon : (Finset.univ : Finset β).Nonempty := by
    exact ⟨⟨x, hx, le_rfl⟩, Finset.mem_univ _⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset β) score hnon
  refine ⟨a.1, a.2.1, a.2.2, ?_⟩
  intro z hz hyz
  let b : β := ⟨z, hz, a.2.2.trans hyz⟩
  by_contra hn
  have hsub : s a.1 ⊂ s b.1 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro w hw
      change w ∈ Finset.univ.filter (fun w => Q w ∧ w ≤ a.1) at hw
      have hw' := Finset.mem_filter.mp hw
      change w ∈ Finset.univ.filter (fun w => Q w ∧ w ≤ b.1)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨hw'.2.1, hw'.2.2.trans hyz⟩⟩
    · intro heq
      have hbmem : b.1 ∈ s b.1 := by
        change b.1 ∈ Finset.univ.filter (fun w => Q w ∧ w ≤ b.1)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b.2.1, le_rfl⟩⟩
      have hamem : b.1 ∈ s a.1 := by
        rw [heq]
        exact hbmem
      change b.1 ∈ Finset.univ.filter (fun w => Q w ∧ w ≤ a.1) at hamem
      have hba := Finset.mem_filter.mp hamem
      exact hn hba.2.2
  have hlt : score a < score b := Finset.card_lt_card hsub
  have hle : score b ≤ score a := hmax b (Finset.mem_univ b)
  omega