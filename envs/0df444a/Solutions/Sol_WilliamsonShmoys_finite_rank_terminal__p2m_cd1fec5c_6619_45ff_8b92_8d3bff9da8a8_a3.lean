-- Prove2me | solution 1 for WilliamsonShmoys.finite_rank_terminal__p2m_cd1fec5c_6619_45ff_8b92_8d3bff9da8a8_a3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-14T04:49:28.194601+00:00
-- url     : https://prove2.me/submissions/c3fba76f-f385-4d1f-9868-6cc9068dc6b3

import Mathlib


theorem solution {α : Type} (good terminal : α → Prop) (rank : α → Nat) (bound : Nat)
    (step preserves : α → α → Prop) (hrefl : ∀ x, preserves x x)
    (htrans : ∀ {x y z}, preserves x y → preserves y z → preserves x z)
    (hbound : ∀ x, rank x ≤ bound)
    (hstep : ∀ x, good x → ¬ terminal x →
      ∃ y, step x y ∧ good y ∧ preserves x y ∧ rank x < rank y)
    (x : α) (hx : good x) :
    ∃ y, Relation.ReflTransGen step x y ∧ preserves x y ∧ good y ∧ terminal y := by
  classical
  have key : ∀ k : ℕ, ∀ x : α, good x → bound - rank x ≤ k →
      ∃ y, Relation.ReflTransGen step x y ∧ preserves x y ∧ good y ∧ terminal y := by
    intro k
    induction k with
    | zero =>
      intro x hx hle
      by_cases hterm : terminal x
      · exact ⟨x, Relation.ReflTransGen.refl, hrefl x, hx, hterm⟩
      · obtain ⟨y, _, hgoody, _, hlt⟩ := hstep x hx hterm
        have := hbound y
        omega
    | succ k ih =>
      intro x hx hle
      by_cases hterm : terminal x
      · exact ⟨x, Relation.ReflTransGen.refl, hrefl x, hx, hterm⟩
      · obtain ⟨y, hstepxy, hgoody, hpres, hlt⟩ := hstep x hx hterm
        have hltk : bound - rank y ≤ k := by
          have := hbound y
          omega
        obtain ⟨z, hrtz, hpresz, hgoodz, htermz⟩ := ih y hgoody hltk
        exact ⟨z, Relation.ReflTransGen.head hstepxy hrtz, htrans hpres hpresz,
          hgoodz, htermz⟩
  exact key (bound - rank x) x hx le_rfl
