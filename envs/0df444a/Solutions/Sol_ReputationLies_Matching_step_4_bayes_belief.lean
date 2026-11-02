-- Prove2me | solution 1 for ReputationLies.Matching.step_4_bayes_belief
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:58:09.987313+00:00
-- url     : https://prove2.me/submissions/8f6d589d-3f26-4146-b92f-c9a929c4c4df

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set MeasureTheory ProbabilityTheory ReputationLies.Matching

namespace RepLiesStep4Aux

theorem cdf_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Continuous (fun b => (μ (Iic b)).toReal) := by
  have heq : (fun b => (μ (Iic b)).toReal) = cdf μ := by
    funext b; rw [cdf_eq_real]; rfl
  rw [heq, continuous_iff_continuousAt]
  intro a
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, ((cdf μ).right_continuous a).mono Ioi_subset_Ici_self⟩
  rw [(Monotone.continuousWithinAt_Iio_iff_leftLim_eq (cdf μ).mono)]
  have h1 := (cdf μ).measure_singleton a
  rw [measure_cdf, measure_singleton] at h1
  have h2 : Function.leftLim (cdf μ) a ≤ cdf μ a := (cdf μ).mono.leftLim_le le_rfl
  have h3 : cdf μ a - Function.leftLim (cdf μ) a ≤ 0 := ENNReal.ofReal_eq_zero.mp h1.symm
  linarith

end RepLiesStep4Aux

open RepLiesStep4Aux in
theorem solution (P : Primitives) (hP : P.Standing) :
    (∀ (σ : Profile) (bstar : ℝ), bstar ∈ Ioc (0 : ℝ) 1 →
      Measurable (fun b => σ.σA b true) → Measurable (fun b => σ.σA b false) →
      (∀ b ∈ Icc (0 : ℝ) 1, σ.σA b true = true) →
      (∀ b ∈ Icc (0 : ℝ) 1, (σ.σA b false = true ↔ bstar < b)) →
      bayesBelief P σ true = P.sRof bstar) ∧
    StrictMonoOn P.sRof (Icc 0 1) ∧ ContinuousOn P.sRof (Icc 0 1) ∧
    P.sRof 0 = P.shat ∧ P.sRof 1 = P.sH := by
  obtain ⟨hsL, hsLH, hsH1, hp0, hp1, -, -, -, -, -, -, -, hμB, hμB1, hnull, hZ, -⟩ := hP
  have hcompl : P.μB (Icc (0:ℝ) 1)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (measure_ne_top _ _), hμB1, measure_univ]; simp
  have hIic1 : P.μB (Iic 1) = 1 := by
    apply le_antisymm prob_le_one
    rw [← hμB1]; exact measure_mono Icc_subset_Iic_self
  have hZ1 : P.Z 1 = 1 := by simp [Primitives.Z, hIic1]
  have hZ0 : P.Z 0 = 0 := by
    have : P.μB (Iic 0) = 0 := by
      rw [← measure_inter_conull (s := Iic 0) hcompl]
      have : Iic (0:ℝ) ∩ Icc 0 1 = {0} := by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2, -⟩; linarith
        · rintro rfl; norm_num
      rw [this, measure_singleton]
    simp [Primitives.Z, this]
  have hZle : ∀ b, P.Z b ≤ 1 := fun b =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hZnn : ∀ b, 0 ≤ P.Z b := fun b => ENNReal.toReal_nonneg
  have hD : ∀ b, 0 < P.p + (1 - P.p) * (1 - P.Z b) := fun b => by
    have := hZle b; nlinarith
  have hform : ∀ b, P.sRof b = P.sL + P.p * (P.sH - P.sL) / (P.p + (1 - P.p) * (1 - P.Z b)) := by
    intro b
    have := (hD b).ne'
    unfold Primitives.sRof
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ bstar hb _ _ hAt hAf
    have hrt : recProb P σ true = 1 := by
      unfold recProb
      have : P.μB {b | σ.σA b true = true} = 1 := by
        apply le_antisymm prob_le_one
        rw [← hμB1]
        exact measure_mono (fun b hb => hAt b hb)
      simp [this]
    have hrf : recProb P σ false = 1 - P.Z bstar := by
      unfold recProb
      have hSI : {b | σ.σA b false = true} ∩ Icc 0 1 = Ioc bstar 1 := by
        ext b
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_Ioc]
        constructor
        · rintro ⟨h, h0, h1⟩
          exact ⟨(hAf b ⟨h0, h1⟩).1 h, h1⟩
        · rintro ⟨h, h1⟩
          have h0 : 0 ≤ b := le_trans hb.1.le h.le
          exact ⟨(hAf b ⟨h0, h1⟩).2 h, h0, h1⟩
      have hset : Ioc bstar 1 = Iic 1 \ Iic bstar := by
        ext x; simp only [mem_Ioc, mem_sdiff, mem_Iic, not_le]; exact and_comm
      rw [← measure_inter_conull hcompl, hSI, hset, measure_sdiff (Iic_subset_Iic.mpr hb.2)
        measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _), hIic1,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
      simp [Primitives.Z]
    unfold bayesBelief msgProb Primitives.sRof
    simp only [sendProb, if_true, hrt, hrf]
    ring_nf
  · intro a ha b hb hab
    have hZab := hZ ha hb hab
    rw [hform a, hform b]
    have hk : 0 < P.p * (P.sH - P.sL) := mul_pos hp0 (by linarith)
    have : P.p + (1 - P.p) * (1 - P.Z b) < P.p + (1 - P.p) * (1 - P.Z a) := by nlinarith
    have := div_lt_div_of_pos_left hk (hD b) this
    linarith
  · apply Continuous.continuousOn
    have hc : Continuous P.Z := cdf_cont P.μB
    unfold Primitives.sRof
    exact (by fun_prop : Continuous fun b => P.p * P.sH + (1 - P.p) * (1 - P.Z b) * P.sL).div
      (by fun_prop) (fun b => (hD b).ne')
  · unfold Primitives.sRof Primitives.shat
    rw [hZ0]; ring_nf
  · unfold Primitives.sRof
    rw [hZ1]; simp only [sub_self, mul_zero, zero_mul, add_zero]; field_simp
