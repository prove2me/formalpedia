-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_maximal_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:16:53.431718+00:00
-- url     : https://prove2.me/submissions/eca1251b-88f2-4114-8b00-89d145903e81

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type}
    (R : α → α → Prop)
    (m : α → Nat)
    (N : Nat)
    (P : α → Prop)
    (hbound : ∀ a : α, P a → m a ≤ N)
    (hstrict : ∀ a b : α, R a b → a ≠ b → m a < m b)
    (a0 : α)
    (ha0 : P a0) :
    ∃ a : α, P a ∧ ∀ b : α, R a b → P b → b = a := by
  classical
  let s : Finset Nat :=
    (Finset.range (N + 1)).filter (fun n => ∃ a : α, P a ∧ m a = n)
  have hmem0 : m a0 ∈ s := by
    change m a0 ∈ Finset.filter (fun n => ∃ a : α, P a ∧ m a = n)
      (Finset.range (N + 1))
    rw [Finset.mem_filter, Finset.mem_range]
    have hbound0 : m a0 ≤ N := hbound a0 ha0
    exact ⟨by omega, ⟨a0, ha0, rfl⟩⟩
  have hs : s.Nonempty := ⟨m a0, hmem0⟩
  let k : Nat := s.max' hs
  have hkmem : k ∈ s := Finset.max'_mem s hs
  have hkwitness : ∃ a : α, P a ∧ m a = k := by
    have h := hkmem
    change k ∈ Finset.filter (fun n => ∃ a : α, P a ∧ m a = n)
      (Finset.range (N + 1)) at h
    exact (Finset.mem_filter.mp h).2
  rcases hkwitness with ⟨a, ha, hma⟩
  refine ⟨a, ha, ?_⟩
  intro b hab hpb
  have hbmem : m b ∈ s := by
    change m b ∈ Finset.filter (fun n => ∃ a : α, P a ∧ m a = n)
      (Finset.range (N + 1))
    rw [Finset.mem_filter, Finset.mem_range]
    have hboundb : m b ≤ N := hbound b hpb
    exact ⟨by omega, ⟨b, hpb, rfl⟩⟩
  have hble : m b ≤ k := by
    dsimp [k]
    exact Finset.le_max' s (m b) hbmem
  by_contra hne
  have hne' : a ≠ b := fun hab' => hne hab'.symm
  have hlt := hstrict a b hab hne'
  omega