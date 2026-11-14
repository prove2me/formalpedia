-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.unit_priority_omission_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:51:45.477862+00:00
-- url     : https://prove2.me/submissions/16c43501-2893-4a77-88ce-c520f4bc4fa7

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    unitPriorityMeasure (Ioi (1 - ε / 2)) = ENNReal.ofReal (ε / 2) := by
  unfold unitPriorityMeasure
  rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  have hinter : Icc (0 : ℝ) 1 ∩ Ioi (1 - ε / 2) = Ioc (1 - ε / 2) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨h0,h1⟩,hx⟩
      exact ⟨hx,h1⟩
    · rintro ⟨hx,h1⟩
      have hx0 : 0 ≤ x := by linarith
      exact ⟨⟨hx0,h1⟩,hx⟩
  rw [hinter, Real.volume_Icc, Real.volume_Ioc]
  norm_num
