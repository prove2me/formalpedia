-- Prove2me | solution 1 for SpecActions.prop1_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @naimengye
-- created : 2026-09-11T15:44:08.201323+00:00
-- url     : https://prove2.me/submissions/109aaa22-53c5-4981-945c-37fa8abfa402

import Theorems.Thm_SpecActions_hits_closed_form

open SpecActions

/-- Proposition 1: the finite-horizon latency ratio of breadth-focused
speculation, obtained from the closed form of the hit count. -/
theorem solution (T : ℕ) (α β pk : ℝ) (hT : 1 ≤ T)
    (hα : 0 < α) (hβ : 0 < β) (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    specTime T α β pk / seqTime T β
      = 1 - (1 / (T : ℝ)) * (α / (α + β)) *
          (((T : ℝ) - 1) * pk / (1 + pk)
            + pk ^ 2 / (1 + pk) ^ 2
            - pk ^ 2 / (1 + pk) ^ 2 * (-pk) ^ (T - 1)) := by
  have hT0 : (0:ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hT0
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hab : (0:ℝ) < α + β := by linarith
  have habne : α + β ≠ 0 := ne_of_gt hab
  have hpne : (1:ℝ) + pk ≠ 0 := by positivity
  -- `T - 1` is natural subtraction; with `1 ≤ T` its cast is the real `T - 1`.
  have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    have : (1:ℕ) ≤ T := hT
    push_cast [Nat.cast_sub this]
    ring
  -- Expand the hit count by the closed form of the recursion.
  have hclosed := hits_closed_form pk hpk0 (T - 1)
  rw [hcast] at hclosed
  simp only [specTime, seqTime, hclosed]
  field_simp
  ring
