-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.first_mask_single_flip_probability_balance
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:37:10.115642+00:00
-- url     : https://prove2.me/submissions/36d7cd85-c281-4d4a-bed6-bb7b83ca30b6

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

private theorem included_probability (ε : ℝ) (hε0 : 0 ≤ ε) :
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

private theorem excluded_probability (ε : ℝ) (hε1 : ε ≤ 1) :
    unitPriorityMeasure (Ioi (1 - ε / 2)) = ENNReal.ofReal (ε / 2) := by
  unfold unitPriorityMeasure
  rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  have he : Icc (0 : ℝ) 1 ∩ Ioi (1 - ε / 2) = Ioc (1 - ε / 2) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨_,hx⟩,hl⟩; exact ⟨hl,hx⟩
    · rintro ⟨hl,hx⟩; exact ⟨⟨by linarith,hx⟩,hl⟩
  rw [he,Real.volume_Icc,Real.volume_Ioc]
  norm_num

theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (m : α → Bool) (c : α) :
    (ε / 2) * (Measure.pi (fun _ : α => unitPriorityMeasure)
      (Set.univ.pi (fun i => if Function.update m c true i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))).toReal =
    (1 - ε / 2) * (Measure.pi (fun _ : α => unitPriorityMeasure)
      (Set.univ.pi (fun i => if Function.update m c false i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))).toReal := by
  classical
  haveI : IsProbabilityMeasure unitPriorityMeasure := by
    unfold unitPriorityMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  let w : Bool → ℝ := fun b => if b then 1 - ε / 2 else ε / 2
  have hw (b : Bool) : (unitPriorityMeasure (if b then Iic (1 - ε / 2) else Ioi (1 - ε / 2))).toReal = w b := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [excluded_probability ε hε1, ENNReal.toReal_ofReal (by linarith)]
      rfl
    · simp only [↓reduceIte]
      rw [included_probability ε hε0, ENNReal.toReal_ofReal (by linarith)]
      rfl
  have hprod (b : Bool) :
      (Measure.pi (fun _ : α => unitPriorityMeasure)
        (Set.univ.pi (fun i => if Function.update m c b i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))).toReal =
      w b * ∏ i ∈ Finset.univ.erase c, w (m i) := by
    rw [Measure.pi_pi, ENNReal.toReal_prod]
    simp_rw [hw]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => w (Function.update m c b i)) (Finset.mem_univ c)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hic : i ≠ c := (Finset.mem_erase.mp hi).1
    simp [Function.update_of_ne hic]
  rw [hprod true, hprod false]
  dsimp [w]
  ring
