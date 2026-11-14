-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.conditional_shifted_exponential_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:43.303377+00:00
-- url     : https://prove2.me/submissions/3237bb28-5de1-424f-8232-6d42362b606b

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

private theorem exponential_tail (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    (expMeasure β).real (Ioi t) = Real.exp (-β * t) := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  have hc : (expMeasure β).real (Iic t) = 1 - Real.exp (-(β * t)) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq hβ t]
    simp [ht]
  have hh := measureReal_compl (μ := expMeasure β) (s := Iic t) measurableSet_Iic
  simp only [compl_Iic, Measure.real, measure_univ, ENNReal.toReal_one] at hh
  change (expMeasure β).real (Ioi t) = 1 - (expMeasure β).real (Iic t) at hh
  rw [hc] at hh
  simpa [neg_mul] using hh

private theorem conditional_shifted_exponential_tail (β d t : ℝ) (hβ : 0 < β) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    ((ProbabilityTheory.cond (expMeasure β) (Ioi d)).map (fun x : ℝ => x - d)).real (Ioi t) =
      (expMeasure β).real (Ioi t) := by
  have hs : Ioi d ∩ (fun x : ℝ => x - d) ⁻¹' Ioi t = Ioi (d+t) := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_preimage]
    constructor
    · rintro ⟨_,hx⟩; linarith
    · intro hx; constructor <;> linarith
  have hm : Measurable (fun x : ℝ => x-d) := measurable_id.sub_const d
  rw [Measure.real, Measure.map_apply hm measurableSet_Ioi,
    ProbabilityTheory.cond_apply measurableSet_Ioi, hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((expMeasure β).real (Ioi d))⁻¹ * (expMeasure β).real (Ioi (d+t)) = _
  rw [exponential_tail β d hβ hd, exponential_tail β (d+t) hβ (by linarith),
    exponential_tail β t hβ ht]
  have he : -β * d + (-β * t) = -β * (d+t) := by ring
  rw [← he, Real.exp_add]
  field_simp

theorem solution (β d : ℝ) (hβ : 0 < β) (hd : 0 ≤ d) :
    (ProbabilityTheory.cond (expMeasure β) (Ioi d)).map (fun x : ℝ => x - d) = expMeasure β := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  have hdreal : (expMeasure β).real (Ioi d) = Real.exp (-β*d) := exponential_tail β d hβ hd
  have hdne : (expMeasure β) (Ioi d) ≠ 0 := by
    intro h
    rw [Measure.real,h,ENNReal.toReal_zero] at hdreal
    exact (ne_of_gt (Real.exp_pos _)) hdreal.symm
  have hdtop : (expMeasure β) (Ioi d) ≠ ⊤ := measure_ne_top _ _
  let ν := ProbabilityTheory.cond (expMeasure β) (Ioi d)
  let g : ℝ → ℝ := fun x => x-d
  have hg : Measurable g := measurable_id.sub_const d
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure_of_finite hdne hdtop
  letI : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have htail (t : ℝ) : (ν.map g).real (Ioi t) = (expMeasure β).real (Ioi t) := by
    by_cases ht : 0 ≤ t
    · exact conditional_shifted_exponential_tail β d t hβ hd ht
    · have ht' : t < 0 := lt_of_not_ge ht
      have hset : Ioi d ∩ g ⁻¹' Ioi t = Ioi d := by
        ext x
        simp only [mem_inter_iff, mem_Ioi, mem_preimage, g]
        constructor
        · exact And.left
        · intro hx; constructor <;> linarith
      have hv : (ν.map g) (Ioi t) = 1 := by
        rw [Measure.map_apply hg measurableSet_Ioi]
        change (ProbabilityTheory.cond (expMeasure β) (Ioi d)) (g ⁻¹' Ioi t) = 1
        rw [ProbabilityTheory.cond_apply measurableSet_Ioi, hset, ENNReal.inv_mul_cancel hdne hdtop]
      have hv' : (expMeasure β).real (Ioi t) = 1 := by
        have hc : (expMeasure β).real (Iic t) = 0 := by
          rw [← cdf_eq_real, cdf_expMeasure_eq hβ t]
          simp [not_le_of_gt ht']
        have hh := measureReal_compl (μ := expMeasure β) (s := Iic t) measurableSet_Iic
        simp only [compl_Iic, Measure.real, measure_univ, ENNReal.toReal_one] at hh
        change (expMeasure β).real (Ioi t) = 1 - (expMeasure β).real (Iic t) at hh
        linarith
      rw [Measure.real,hv,ENNReal.toReal_one,hv']
  apply Measure.ext_of_Iic
  intro t
  have hm := measureReal_compl (μ := ν.map g) (s := Ioi t) measurableSet_Ioi
  have he := measureReal_compl (μ := expMeasure β) (s := Ioi t) measurableSet_Ioi
  have hr : (ν.map g).real (Iic t) = (expMeasure β).real (Iic t) := by
    have h1 : (ν.map g).real univ = 1 := by simp [Measure.real]
    have h2 : (expMeasure β).real univ = 1 := by simp [Measure.real]
    rw [compl_Ioi,h1,htail] at hm
    rw [compl_Ioi,h2] at he
    linarith
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (ν.map g) _) (measure_ne_top (expMeasure β) _)).mp
  exact hr
