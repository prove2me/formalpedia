-- Prove2me | solution 1 for ViceGoals.Personal.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:42:01.529439+00:00
-- url     : https://prove2.me/submissions/b079510d-6431-4f8b-bde6-8a24df53547d

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model
open ViceGoals.Personal

theorem solution(m : Params) (hm : m.Standing) (p q : ℝ) (hp : 0 ≤ p) :
    IsOptQtyB m p q ↔
      q = if p ≤ m.v - m.beta * m.h then m.v - m.beta * m.h - p else 0 := by
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
  exact key p q
