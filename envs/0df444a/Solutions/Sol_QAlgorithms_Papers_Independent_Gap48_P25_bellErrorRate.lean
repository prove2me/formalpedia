-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.bellErrorRate
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T23:16:51.37536+00:00
-- url     : https://prove2.me/submissions/8053a991-b333-4386-bbcc-14971bb43157

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)


namespace P25BellH
open QAlgorithms

lemma smono : StrictMonoOn QAlgorithms.binEntropy2 (Set.Icc (0:ℝ) (1/2)) := by
  intro a ha b hb hab
  unfold QAlgorithms.binEntropy2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : (1/2:ℝ) = 2⁻¹ := by norm_num
  rw [this] at ha hb
  exact div_lt_div_of_pos_right (Real.binEntropy_strictMonoOn ha hb hab) hl

lemma cont : Continuous QAlgorithms.binEntropy2 := by
  unfold QAlgorithms.binEntropy2
  exact Real.binEntropy_continuous.div_const _

lemma g0 : QAlgorithms.binEntropy2 0 = 0 := by simp [QAlgorithms.binEntropy2]
lemma ghalf : QAlgorithms.binEntropy2 (1/2) = 1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : (1/2:ℝ) = 2⁻¹ := by norm_num
  simp only [QAlgorithms.binEntropy2, this, Real.binEntropy_two_inv]
  exact div_self hl.ne'

end P25BellH

/-- Eq.(B3), PDF p.47: computed Bell error and assigned mean-cycle yield.
The approximate decimal threshold is replaced by its implicit entropy definition. -/
theorem solution (R F : ℝ) (hR : 0 ≤ R) (hF : F ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i, 0 ≤ bellLaw F i) ∧ (∑ i : Fin 4, bellLaw F i) = 1 ∧
    bellError F = (2/3)*(1-F) ∧
    repeaterKey R F = R*(1-2*QAlgorithms.binEntropy2 ((2/3)*(1-F))) ∧
    max (repeaterKey R F) 0 = R*max (1-2*QAlgorithms.binEntropy2 ((2/3)*(1-F))) 0 ∧
    ∃ q : ℝ, 0 < q ∧ q < 1/2 ∧ QAlgorithms.binEntropy2 q = 1/2 ∧
      (∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) (1/2) → (QAlgorithms.binEntropy2 z = 1/2 ↔ z = q)) ∧
      (1/4 ≤ F → (0 < repeaterKey R F ↔ 0 < R ∧ 1-(3/2)*q < F)) := by
  have hF0 := hF.1
  have hF1 := hF.2
  have hbe : bellError F = (2/3)*(1-F) := by
    simp [bellError, Fin.sum_univ_four, bellLaw]; ring
  have hrk : repeaterKey R F = R*(1-2*QAlgorithms.binEntropy2 ((2/3)*(1-F))) := by
    unfold repeaterKey signedRate; rw [hbe]; ring
  obtain ⟨q, hqI, hq⟩ : ∃ q ∈ Set.Icc (0:ℝ) (1/2), QAlgorithms.binEntropy2 q = 1/2 := by
    have := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1/2) P25BellH.cont.continuousOn
    rw [P25BellH.g0, P25BellH.ghalf] at this
    exact this ⟨by norm_num, by norm_num⟩
  have hq0 : q ≠ 0 := by rintro rfl; rw [P25BellH.g0] at hq; norm_num at hq
  have hq1 : q ≠ 1/2 := by rintro rfl; rw [P25BellH.ghalf] at hq; norm_num at hq
  refine ⟨fun i => ?_, ?_, hbe, hrk, ?_, q, lt_of_le_of_ne hqI.1 (Ne.symm hq0),
    lt_of_le_of_ne hqI.2 hq1, hq, fun z hz => ?_, fun h4 => ?_⟩
  · unfold bellLaw; split_ifs <;> linarith
  · simp [Fin.sum_univ_four, bellLaw]; ring
  · rw [hrk, mul_max_of_nonneg _ _ hR, mul_zero]
  · constructor
    · intro hz2; exact P25BellH.smono.injOn hz hqI (hz2.trans hq.symm)
    · rintro rfl; exact hq
  · rw [hrk]
    have heI : (2/3)*(1-F) ∈ Set.Icc (0:ℝ) (1/2) := ⟨by nlinarith, by nlinarith⟩
    have key : 0 < 1-2*QAlgorithms.binEntropy2 ((2/3)*(1-F)) ↔ 1-(3/2)*q < F := by
      rw [show (0 < 1-2*QAlgorithms.binEntropy2 ((2/3)*(1-F))) ↔
        QAlgorithms.binEntropy2 ((2/3)*(1-F)) < QAlgorithms.binEntropy2 q from by
          rw [hq]; constructor <;> intro h <;> linarith]
      rw [P25BellH.smono.lt_iff_lt heI hqI]
      constructor <;> intro h <;> linarith
    rw [← key]
    constructor
    · intro h
      rcases hR.lt_or_eq with hR' | hR'
      · exact ⟨hR', (pos_iff_pos_of_mul_pos h).1 hR'⟩
      · rw [← hR'] at h; simp at h
    · rintro ⟨a, b⟩; exact mul_pos a b




