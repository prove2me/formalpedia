-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.outside_priority_conditional_eq_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:24:01.787299+00:00
-- url     : https://prove2.me/submissions/304d20b6-4f09-441c-ac5c-d80bfb111680

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
import Theorems.Thm_StabilityDichotomies_Bijunctive_condition_finite_product_on_rectangle
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem solution (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ProbabilityTheory.cond unitPriorityMeasure (Ioi (1 - ε / 2)) = cutoffMeasure ε := by
  have ha : (0 : ℝ) ≤ 1 - ε / 2 := by linarith
  have hfinite : volume (Icc (0 : ℝ) 1) ≠ ⊤ := by simp
  unfold unitPriorityMeasure cutoffMeasure
  rw [ProbabilityTheory.cond_cond_eq_cond_inter' measurableSet_Icc measurableSet_Ioi hfinite]
  have he : Icc (0 : ℝ) 1 ∩ Ioi (1 - ε / 2) = Ioc (1 - ε / 2) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨_, hx⟩, hl⟩; exact ⟨hl,hx⟩
    · rintro ⟨hl,hx⟩; exact ⟨⟨le_trans ha (le_of_lt hl),hx⟩,hl⟩
  rw [he]
  have hae : Ioc (1 - ε / 2) 1 =ᵐ[volume] Icc (1 - ε / 2) 1 := Ioc_ae_eq_Icc
  unfold ProbabilityTheory.cond
  rw [measure_congr hae, Measure.restrict_congr_set hae]

