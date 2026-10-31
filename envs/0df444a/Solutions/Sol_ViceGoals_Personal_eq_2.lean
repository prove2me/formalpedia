-- Prove2me | solution 1 for ViceGoals.Personal.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:42:12.478996+00:00
-- url     : https://prove2.me/submissions/4269d265-b0b6-4170-8f0d-9bf119e32682

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model
open ViceGoals.Personal

theorem solution(m : Params) (hm : m.Standing) (p Q : ℝ) (hp : 0 ≤ p) :
    IsDemandB m p Q ↔
      Q = if p ≤ pbarB m then m.v - m.beta * m.h - p else 0 := by
  have key : ∀ p q : ℝ, (IsOptQtyB m p q ↔
      q = if p ≤ m.v - m.beta * m.h then m.v - m.beta * m.h - p else 0) := by
    intro p q
    have hU : ∀ x, U4B m p x = (m.v - m.beta * m.h - p) * x - x ^ 2 / 2 := by
      intro x; unfold U4B; ring
    unfold IsOptQtyB
    simp only [hU]
    split_ifs with ha
    · constructor
      · rintro ⟨hq, h⟩
        have := h (m.v - m.beta * m.h - p) (by linarith)
        nlinarith [sq_nonneg (q - (m.v - m.beta * m.h - p))]
      · rintro rfl
        refine ⟨by linarith, fun q' _ => ?_⟩
        nlinarith [sq_nonneg (q' - (m.v - m.beta * m.h - p))]
    · push Not at ha
      constructor
      · rintro ⟨hq, h⟩
        have := h 0 le_rfl
        nlinarith
      · rintro rfl
        refine ⟨le_rfl, fun q' hq' => ?_⟩
        nlinarith
  obtain ⟨hv, hb0, hb1, hh, hl⟩ := hm
  have hU2 : ∀ x, U2B m p x = (m.v - m.h - p) * x - x ^ 2 / 2 := by
    intro x; unfold U2B; ring
  have hpb : pbarB m ≤ m.v - m.beta * m.h := by unfold pbarB; nlinarith
  unfold IsDemandB
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [key] at hq
    rw [hU2]
    by_cases ha : p ≤ m.v - m.beta * m.h
    · rw [if_pos ha] at hq; subst hq
      by_cases hb : p ≤ pbarB m
      · rw [if_pos hb, if_pos]; unfold pbarB at hb; nlinarith
      · rw [if_neg hb]; unfold pbarB at hb; push Not at hb
        split_ifs with hc
        · nlinarith
        · rfl
    · rw [if_neg ha] at hq; subst hq
      have hnb : ¬ p ≤ pbarB m := fun h => ha (le_trans h hpb)
      rw [if_neg hnb]; split_ifs <;> rfl
  · intro hQ
    refine ⟨if p ≤ m.v - m.beta * m.h then m.v - m.beta * m.h - p else 0, (key p _).2 rfl, ?_⟩
    rw [hQ, hU2]
    by_cases ha : p ≤ m.v - m.beta * m.h
    · rw [if_pos ha]
      by_cases hb : p ≤ pbarB m
      · rw [if_pos hb, if_pos]; unfold pbarB at hb; nlinarith
      · rw [if_neg hb]; unfold pbarB at hb; push Not at hb
        split_ifs with hc
        · nlinarith
        · rfl
    · have hnb : ¬ p ≤ pbarB m := fun h => ha (le_trans h hpb)
      rw [if_neg ha, if_neg hnb]; split_ifs <;> rfl
