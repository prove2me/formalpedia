-- Prove2me | solution 1 for WilliamsonShmoys.finite_rank_extension_reaches_terminal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:07:56.564989+00:00
-- url     : https://prove2.me/submissions/e568d144-486a-4a02-a142-6c0e5177361f

import Mathlib

set_option autoImplicit false
theorem solution
    {α : Type} (rank : α → Nat) (P T : α → Prop) (a : α) (B : Nat)
    (ha : P a) (haB : rank a ≤ B)
    (hstep : ∀ x : α, P x → ¬ T x →
      ∃ y : α, P y ∧ rank x < rank y ∧ rank y ≤ B) :
    ∃ x : α, P x ∧ T x := by
  have key : ∀ n : Nat, ∀ x : α, P x → rank x ≤ B → B - rank x ≤ n → ∃ x : α, P x ∧ T x := by
    intro n
    induction n with
    | zero =>
      intro x hx hxB hn
      by_contra hc
      push_neg at hc
      obtain ⟨y, -, hy1, hy2⟩ := hstep x hx (hc x hx)
      omega
    | succ n ih =>
      intro x hx hxB hn
      by_cases hT : T x
      · exact ⟨x, hx, hT⟩
      obtain ⟨y, hy, hy1, hy2⟩ := hstep x hx hT
      exact ih y hy hy2 (by omega)
  exact key _ a ha haB le_rfl
