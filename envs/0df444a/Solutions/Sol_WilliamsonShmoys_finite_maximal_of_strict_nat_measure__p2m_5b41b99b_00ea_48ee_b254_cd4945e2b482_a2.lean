-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_of_strict_nat_measure__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:24.912851+00:00
-- url     : https://prove2.me/submissions/09b25099-f9ab-4f03-9904-ee80d34f118a

import Mathlib
set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (μ : α → ℕ)
    (hstrict : ∀ ⦃a b : α⦄, a ≤ b → a ≠ b → μ a < μ b)
    (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by
  classical
  let s : Finset ℕ := Finset.univ.image (fun a : {x // P x} => μ a.1)
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    refine ⟨μ a, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩
  let m : ℕ := s.max' hs
  have hm : m ∈ s := Finset.max'_mem s hs
  obtain ⟨a', _, hμ⟩ := Finset.mem_image.mp hm
  refine ⟨a'.1, a'.2, ?_⟩
  intro b hb hab
  have hbmem : μ b ∈ s := by
    exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩
  have hmax : μ b ≤ m := by
    exact Finset.le_max' s (μ b) hbmem
  by_contra hneq
  have hlt := hstrict hab (by
    intro heq
    exact hneq heq.symm)
  omega