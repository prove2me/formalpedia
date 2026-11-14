-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.conditional_first_mask_priority_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:24:44.049883+00:00
-- url     : https://prove2.me/submissions/2d2c8065-89c6-47a3-9d32-1d966b15b970

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
import Theorems.Thm_StabilityDichotomies_Bijunctive_condition_finite_product_on_rectangle
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem outside_priority_conditional_eq_cutoff (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
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

private theorem included_priority_probability (ε : ℝ) (hε1 : ε ≤ 1) (hε0 : 0 ≤ ε) :
    unitPriorityMeasure (Iic (1 - ε / 2)) = ENNReal.ofReal (1 - ε / 2) := by
  unfold unitPriorityMeasure
  rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  have he : Icc (0 : ℝ) 1 ∩ Iic (1 - ε / 2) = Icc 0 (1 - ε / 2) := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · rintro ⟨⟨h0,h1⟩,h⟩; exact ⟨h0,h⟩
    · rintro ⟨h0,h⟩; exact ⟨⟨h0,by linarith⟩,h⟩
  rw [he,Real.volume_Icc,Real.volume_Icc]
  norm_num

theorem solution {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool) :
    ProbabilityTheory.cond (Measure.pi (fun _ : α => unitPriorityMeasure))
      (Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) =
    Measure.pi (fun i => if m i then ProbabilityTheory.cond unitPriorityMeasure (Iic (1 - ε / 2))
      else cutoffMeasure ε) := by
  classical
  letI : IsProbabilityMeasure unitPriorityMeasure := by
    unfold unitPriorityMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  let s : α → Set ℝ := fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)
  have hs (i : α) : MeasurableSet (s i) := by
    dsimp [s]
    split
    · exact measurableSet_Iic
    · exact measurableSet_Ioi
  have hpos (i : α) : unitPriorityMeasure (s i) ≠ 0 := by
    dsimp [s]
    split
    · rw [included_priority_probability ε hε1 (le_of_lt hε)]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    · unfold unitPriorityMeasure
      rw [ProbabilityTheory.cond_apply measurableSet_Icc]
      have he : Icc (0 : ℝ) 1 ∩ Ioi (1 - ε / 2) = Ioc (1 - ε / 2) 1 := by
        ext x
        simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
        constructor
        · rintro ⟨⟨_,hx⟩,hl⟩; exact ⟨hl,hx⟩
        · rintro ⟨hl,hx⟩; exact ⟨⟨by linarith,hx⟩,hl⟩
      rw [he, Real.volume_Icc, Real.volume_Ioc]
      norm_num
      linarith
  rw [condition_finite_product_on_rectangle (fun _ : α => unitPriorityMeasure) s hs hpos]
  congr 1
  funext i
  dsimp [s]
  split <;> simp_all [outside_priority_conditional_eq_cutoff]
