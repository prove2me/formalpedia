-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_nat_on_bounded_fiber__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:38.625137+00:00
-- url     : https://prove2.me/submissions/d29a7f0c-928d-4f9a-a26a-947d3beaea08

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} (Q : α → Prop) (f : α → Nat) (N : Nat)
    (hbound : ∀ a, Q a → f a ≤ N) (hne : ∃ a, Q a) :
    ∃ a, Q a ∧ ∀ b, Q b → f b ≤ f a := by
  induction N generalizing hne with
  | zero =>
      obtain ⟨a, ha⟩ := hne
      refine ⟨a, ha, ?_⟩
      intro b hb
      have hfa : f a ≤ 0 := hbound a ha
      have hfb : f b ≤ 0 := hbound b hb
      omega
  | succ N ih =>
      by_cases htop : ∃ a, Q a ∧ f a = Nat.succ N
      · obtain ⟨a, ha, hfa⟩ := htop
        refine ⟨a, ha, ?_⟩
        intro b hb
        have hfb : f b ≤ Nat.succ N := hbound b hb
        omega
      · have hbound' : ∀ a, Q a → f a ≤ N := by
          intro a ha
          have hle : f a ≤ Nat.succ N := hbound a ha
          have hneq : f a ≠ Nat.succ N := by
            intro heq
            exact htop ⟨a, ha, heq⟩
          omega
        exact ih hbound' hne