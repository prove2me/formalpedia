-- Prove2me | solution 1 for RobbinsSeqDesign.StayOrSwitch.head_prob_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T13:06:14.043207+00:00
-- url     : https://prove2.me/submissions/184aa31c-5a66-4ac5-80da-b3e1aed71cff

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules
import Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_head_prob_recursion

open MeasureTheory ProbabilityTheory Filter Topology
open RobbinsSeqDesign.StayOrSwitch

theorem solution (α β : unitInterval)
    (hnot0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0)) (hnot1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1))
    (i : ℕ) (hi : 1 ≤ i) :
    headProb ruleR1 α β i =
      ((α : ℝ) + β - 1) ^ (i - 1) *
          (headProb ruleR1 α β 1 - ((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β))) +
        ((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β)) := by
  have ha1 : (α : ℝ) ≤ 1 := α.2.2
  have hb1 : (β : ℝ) ≤ 1 := β.2.2
  have hlt : (α : ℝ) + β < 2 := by
    by_contra h
    exact hnot1 ⟨by linarith, by linarith⟩
  have hne : (2 : ℝ) - (α + β) ≠ 0 := by linarith
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [head_prob_recursion α β hnot0 hnot1 n hn, ih]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
    ring
