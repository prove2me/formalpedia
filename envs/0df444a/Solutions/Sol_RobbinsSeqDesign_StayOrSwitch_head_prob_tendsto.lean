-- Prove2me | solution 1 for RobbinsSeqDesign.StayOrSwitch.head_prob_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T13:06:52.625015+00:00
-- url     : https://prove2.me/submissions/5a89acca-9181-4bd5-8030-fcad23c807ee

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules
import Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_head_prob_closed_form

open MeasureTheory ProbabilityTheory Filter Topology
open RobbinsSeqDesign.StayOrSwitch

theorem solution (α β : unitInterval)
    (hnot0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0)) (hnot1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1)) :
    Tendsto (fun i => headProb ruleR1 α β i) atTop
        (𝓝 (((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β)))) ∧
      ((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β)) =
        gamma α β + delta α β ^ 2 / (1 - gamma α β) := by
  have ha0 : (0 : ℝ) ≤ α := α.2.1
  have hb0 : (0 : ℝ) ≤ β := β.2.1
  have ha1 : (α : ℝ) ≤ 1 := α.2.2
  have hb1 : (β : ℝ) ≤ 1 := β.2.2
  have hlt : (α : ℝ) + β < 2 := by
    by_contra h
    exact hnot1 ⟨by linarith, by linarith⟩
  have hpos : (0 : ℝ) < α + β := by
    by_contra h
    exact hnot0 ⟨by linarith, by linarith⟩
  have hc : |(α : ℝ) + β - 1| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  refine ⟨?_, ?_⟩
  · set L := ((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β))
    set K := headProb ruleR1 α β 1 - L
    have hpow : Tendsto (fun i : ℕ => ((α : ℝ) + β - 1) ^ (i - 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).comp (tendsto_sub_atTop_nat 1)
    have hlim : Tendsto (fun i : ℕ => ((α : ℝ) + β - 1) ^ (i - 1) * K + L) atTop (𝓝 L) := by
      simpa using (hpow.mul_const K).add_const L
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with i hi
    exact (head_prob_closed_form α β hnot0 hnot1 i hi).symm
  · have hne : (2 : ℝ) - (α + β) ≠ 0 := by linarith
    have hne' : (1 : ℝ) - (α + β) / 2 ≠ 0 := by linarith
    simp only [gamma, delta, div_pow, sq_abs]
    field_simp
    ring
