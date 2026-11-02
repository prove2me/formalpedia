-- Prove2me | solution 1 for WilliamsonShmoys.bounded_finite_ascent__p2m_6759599f_0df8_4b6f_bc89_5739bb0b46dc_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:53.599241+00:00
-- url     : https://prove2.me/submissions/bc094f65-e51f-49b0-a348-e183bbd197f0

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} (P Done : α → Prop) (rank : α → ℕ) (bound : ℕ) (x0 : α)
    (hstart : P x0) (hbound : rank x0 ≤ bound)
    (hstep : ∀ x, P x → ¬ Done x →
      ∃ y, P y ∧ rank x < rank y ∧ rank y ≤ bound) :
    ∃ x, P x ∧ Done x := by
  have aux : ∀ m (x : α), bound - rank x = m → P x → rank x ≤ bound →
      ∃ z, P z ∧ Done z := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hm hx hr
      by_cases hd : Done x
      · exact ⟨x, hx, hd⟩
      · obtain ⟨y, hy, hlt, hyb⟩ := hstep x hx hd
        have hsmall : bound - rank y < m := by omega
        exact ih (bound - rank y) hsmall y rfl hy hyb
  exact aux (bound - rank x0) x0 rfl hstart hbound