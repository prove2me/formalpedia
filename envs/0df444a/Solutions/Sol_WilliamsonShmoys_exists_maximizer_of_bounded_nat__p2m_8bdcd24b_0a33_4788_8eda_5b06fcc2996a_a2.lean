-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximizer_of_bounded_nat__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:40:14.522604+00:00
-- url     : https://prove2.me/submissions/cea2fba7-5581-43ec-afa3-dca293cf3052

import Mathlib

theorem exists_max_of_bounded_nat__p2m_a38b79a1_124e_43f5_be2e_7a1970ee2a96_a2
    {α : Type} (P : α → Prop) (size : α → Nat) (N : Nat)
    (hne : ∃ x, P x)
    (hbdd : ∀ x, P x → size x ≤ N) :
    ∃ x, P x ∧ ∀ y, P y → size y ≤ size x := by
  induction N generalizing P size with
  | zero =>
      obtain ⟨x, hx⟩ := hne
      refine ⟨x, hx, ?_⟩
      intro y hy
      have h := hbdd y hy
      omega
  | succ N ih =>
      by_cases htop : ∃ x, P x ∧ size x = Nat.succ N
      · obtain ⟨x, hx, hxs⟩ := htop
        refine ⟨x, hx, ?_⟩
        intro y hy
        have hybdd := hbdd y hy
        omega
      · have hne' : ∃ x, (P x ∧ size x ≤ N) := by
          obtain ⟨x, hx⟩ := hne
          refine ⟨x, hx, ?_⟩
          have hle := hbdd x hx
          by_contra hn
          have heq : size x = Nat.succ N := by omega
          exact htop ⟨x, hx, heq⟩
        have hbdd' : ∀ x, (P x ∧ size x ≤ N) → size x ≤ N := by
          intro x hx
          exact hx.2
        obtain ⟨x, hx, hxmax⟩ :=
          ih (fun z => P z ∧ size z ≤ N) size hne' hbdd'
        refine ⟨x, hx.1, ?_⟩
        intro y hy
        have hle := hbdd y hy
        have hleN : size y ≤ N := by
          by_contra hn
          have heq : size y = Nat.succ N := by omega
          exact htop ⟨y, hy, heq⟩
        exact hxmax y ⟨hy, hleN⟩

theorem solution
    {α : Type} (P : α → Prop) (size : α → Nat)
    (hne : ∃ x, P x)
    (hbdd : ∃ N, ∀ x, P x → size x ≤ N) :
    ∃ x, P x ∧ ∀ y, P y → size y ≤ size x := by
  obtain ⟨N, hN⟩ := hbdd
  exact exists_max_of_bounded_nat__p2m_a38b79a1_124e_43f5_be2e_7a1970ee2a96_a2
    P size N hne hN