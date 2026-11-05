-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_score_member__p2m_456d6f91_af0e_46c2_8bb6_0425e8955342_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:41:04.811962+00:00
-- url     : https://prove2.me/submissions/c4029cc2-9ab3-4763-9ab4-f7b46dd0a7bb

import Mathlib

theorem solution
    {α : Type} [Fintype α]
    (P : α → Prop) (score : α → Nat) (a : α) (ha : P a) :
    ∃ b, P b ∧ ∀ c, P c → score c ≤ score b := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := ⟨a, by simp [s, ha]⟩
  obtain ⟨b, hbs, hbmax⟩ := Finset.exists_max_image s score hs
  refine ⟨b, ?_, ?_⟩
  · simpa [s] using hbs
  · intro c hc
    exact hbmax c (by simp [s, hc])
