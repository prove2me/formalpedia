-- Prove2me | solution 1 for PerishableReturns.Suboptimal.theorem_1_and_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T13:30:14.675083+00:00
-- url     : https://prove2.me/submissions/bc90e57d-5cd9-4c05-8eff-05e33ab5c0e6

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

set_option autoImplicit false

namespace PRSubopt180

open MeasureTheory ProbabilityTheory PerishableReturns.Suboptimal

lemma cdf_continuous (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] :
    Continuous (cdf D) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono := (cdf D).mono
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim, (cdf D).rightLim_eq]
  have h1 : (cdf D).measure {a} = 0 := by
    rw [measure_cdf]; exact MeasureTheory.measure_singleton a
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at h1
  have h2 : Function.leftLim (cdf D) a ≤ cdf D a := hmono.leftLim_le le_rfl
  linarith

lemma cdf_zero (D : Measure ℝ) (hD : IsDemand D) [NullSingletonClass D] : cdf D 0 = 0 := by
  have := hD.isProb
  rw [cdf_eq_real, measureReal_def]
  have : D (Set.Iic 0) = 0 := by
    rw [← Set.Iio_union_right]
    exact measure_union_null hD.nonneg (MeasureTheory.measure_singleton 0)
  simp [this]

lemma real_Ioi (D : Measure ℝ) [IsProbabilityMeasure D] (t : ℝ) :
    D.real (Set.Ioi t) = 1 - cdf D t := by
  rw [cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

lemma int_min (D : Measure ℝ) [IsProbabilityMeasure D] (hX : Integrable (fun x : ℝ => x) D)
    (Q : ℝ) : Integrable (fun x : ℝ => min x Q) D :=
  hX.inf (integrable_const Q)

lemma m_upper (D : Measure ℝ) [IsProbabilityMeasure D] (hX : Integrable (fun x : ℝ => x) D)
    {Q1 Q2 : ℝ} (h : Q1 ≤ Q2) :
    (∫ x, min x Q2 ∂D) - (∫ x, min x Q1 ∂D) ≤ (Q2 - Q1) * (1 - cdf D Q1) := by
  have hind : ∫ x, (Set.Ioi Q1).indicator (fun _ => Q2 - Q1) x ∂D
      = (Q2 - Q1) * (1 - cdf D Q1) := by
    rw [integral_indicator_const _ measurableSet_Ioi, real_Ioi, smul_eq_mul, mul_comm]
  rw [← integral_sub (int_min D hX Q2) (int_min D hX Q1), ← hind]
  refine integral_mono ((int_min D hX Q2).sub (int_min D hX Q1))
    ((integrable_const _).indicator measurableSet_Ioi) ?_
  intro x
  simp only [Set.indicator, Set.mem_Ioi, min_def]
  split_ifs <;> linarith

lemma m_lower (D : Measure ℝ) [IsProbabilityMeasure D] (hX : Integrable (fun x : ℝ => x) D)
    {Q1 Q2 : ℝ} (h : Q1 ≤ Q2) :
    (Q2 - Q1) * (1 - cdf D Q2) ≤ (∫ x, min x Q2 ∂D) - (∫ x, min x Q1 ∂D) := by
  have hind : ∫ x, (Set.Ioi Q2).indicator (fun _ => Q2 - Q1) x ∂D
      = (Q2 - Q1) * (1 - cdf D Q2) := by
    rw [integral_indicator_const _ measurableSet_Ioi, real_Ioi, smul_eq_mul, mul_comm]
  rw [← integral_sub (int_min D hX Q2) (int_min D hX Q1), ← hind]
  refine integral_mono ((integrable_const _).indicator measurableSet_Ioi)
    ((int_min D hX Q2).sub (int_min D hX Q1)) ?_
  intro x
  simp only [Set.indicator, Set.mem_Ioi, min_def]
  split_ifs <;> linarith

lemma nv_upper (D : Measure ℝ) [IsProbabilityMeasure D] (hX : Integrable (fun x : ℝ => x) D)
    {A B C : ℝ} (hA : 0 ≤ A) (f : ℝ → ℝ) {Q1 Q2 : ℝ} (h : Q1 ≤ Q2)
    (h1 : f Q1 = -B * Q1 + A * (∫ x, min x Q1 ∂D) + C)
    (h2 : f Q2 = -B * Q2 + A * (∫ x, min x Q2 ∂D) + C) :
    f Q2 - f Q1 ≤ (Q2 - Q1) * (A * (1 - cdf D Q1) - B) := by
  have hm := mul_le_mul_of_nonneg_left (m_upper D hX h) hA
  rw [h1, h2]
  linarith

lemma nv_lower (D : Measure ℝ) [IsProbabilityMeasure D] (hX : Integrable (fun x : ℝ => x) D)
    {A B C : ℝ} (hA : 0 ≤ A) (f : ℝ → ℝ) {Q1 Q2 : ℝ} (h : Q1 ≤ Q2)
    (h1 : f Q1 = -B * Q1 + A * (∫ x, min x Q1 ∂D) + C)
    (h2 : f Q2 = -B * Q2 + A * (∫ x, min x Q2 ∂D) + C) :
    (Q2 - Q1) * (A * (1 - cdf D Q2) - B) ≤ f Q2 - f Q1 := by
  have hm := mul_le_mul_of_nonneg_left (m_lower D hX h) hA
  rw [h1, h2]
  linarith

lemma EPT_eq (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hX : Integrable (fun x : ℝ => x) D) (Q : ℝ) :
    EPT K D Q = (K.c3 - K.c) * Q + (K.p + K.g2 - K.c3) * (∫ x, min x Q ∂D)
      - K.g2 * (∫ x, x ∂D) := by
  unfold EPT
  rw [integral_congr_ae (g := fun x => ((K.p + K.g2 - K.c3) * min x Q + K.c3 * Q) - K.g2 * x)
    (Filter.Eventually.of_forall fun x => ?_)]
  · have i1 : Integrable (fun x : ℝ => (K.p + K.g2 - K.c3) * min x Q + K.c3 * Q) D :=
      ((int_min D hX Q).const_mul _).add (integrable_const _)
    have i2 : Integrable (fun x : ℝ => K.g2 * x) D := hX.const_mul _
    have e2 : ∫ x, K.g2 * x ∂D = K.g2 * ∫ x, x ∂D := integral_const_mul K.g2 (fun x => x)
    rw [integral_sub i1 i2, e2,
      integral_add ((int_min D hX Q).const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp
    ring
  · simp only [min_def]
    split_ifs <;> ring

lemma EPR1_eq (K : Costs) (c1 : ℝ) (D : Measure ℝ) [IsProbabilityMeasure D] (hD : IsDemand D)
    {Q : ℝ} (hQ : 0 ≤ Q) :
    EPR K c1 c1 1 D Q = (K.p - c1 + K.g) * (∫ x, min x Q ∂D) - K.g * (∫ x, x ∂D) := by
  have hX := hD.integrable
  have hae : ∀ᵐ x ∂D, 0 ≤ x := by
    rw [ae_iff]
    convert hD.nonneg using 2
    ext x
    simp
  unfold EPR
  rw [integral_congr_ae (g := fun x => ((K.p - c1 + K.g) * min x Q + c1 * Q) - K.g * x)
    (hae.mono fun x hx => ?_)]
  · have i1 : Integrable (fun x : ℝ => (K.p - c1 + K.g) * min x Q + c1 * Q) D :=
      ((int_min D hX Q).const_mul _).add (integrable_const _)
    have i2 : Integrable (fun x : ℝ => K.g * x) D := hX.const_mul _
    have e2 : ∫ x, K.g * x ∂D = K.g * ∫ x, x ∂D := integral_const_mul K.g (fun x => x)
    rw [integral_sub i1 i2, e2,
      integral_add ((int_min D hX Q).const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp
    ring
  · simp only [sub_self, zero_mul, min_def]
    split_ifs <;> first
      | (exfalso; linarith)
      | ring1
      | (obtain rfl : x = 0 := by linarith
         ring1)

lemma EPR0_eq (K : Costs) (c1 c2 : ℝ) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hX : Integrable (fun x : ℝ => x) D) (Q : ℝ) :
    EPR K c1 c2 0 D Q = (K.c3 - c1) * Q + (K.p + K.g - K.c3) * (∫ x, min x Q ∂D)
      - K.g * (∫ x, x ∂D) := by
  unfold EPR
  rw [integral_congr_ae (g := fun x => ((K.p + K.g - K.c3) * min x Q + K.c3 * Q) - K.g * x)
    (Filter.Eventually.of_forall fun x => ?_)]
  · have i1 : Integrable (fun x : ℝ => (K.p + K.g - K.c3) * min x Q + K.c3 * Q) D :=
      ((int_min D hX Q).const_mul _).add (integrable_const _)
    have i2 : Integrable (fun x : ℝ => K.g * x) D := hX.const_mul _
    have e2 : ∫ x, K.g * x ∂D = K.g * ∫ x, x ∂D := integral_const_mul K.g (fun x => x)
    rw [integral_sub i1 i2, e2,
      integral_add ((int_min D hX Q).const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp
    ring
  · simp only [sub_zero, one_mul, zero_mul, add_zero, min_def]
    split_ifs <;> first
      | (exfalso; linarith)
      | ring1

end PRSubopt180

open MeasureTheory PerishableReturns.Suboptimal in
theorem solution (K : Costs) (c1 : ℝ) (hc : K.c < c1) (hp : c1 < K.p)
    (D : Measure ℝ) (hD : IsDemand D) [NullSingletonClass D] :
    (∃ Q : ℝ, IsOptimalOrder (EPT K D) Q) ∧
    (∀ Q : ℝ, IsOptimalOrder (EPT K D) Q →
      ¬ IsOptimalOrder (EPR K c1 c1 1 D) Q) ∧
    (∀ c2 Q : ℝ, IsOptimalOrder (EPT K D) Q →
      ¬ IsOptimalOrder (EPR K c1 c2 0 D) Q) := by
  have := hD.isProb
  have hX := hD.integrable
  have hcont := PRSubopt180.cdf_continuous D
  have hF0 := PRSubopt180.cdf_zero D hD
  have hc3 := K.c3_lt_c
  have hcp := K.c_lt_p
  have hg1 : 0 ≤ K.g1 := K.g1_nonneg
  have hg : 0 ≤ K.g := K.g_nonneg
  have hg2def : K.g2 = K.g + K.g1 := rfl
  have hA : 0 < K.p + K.g2 - K.c3 := by linarith
  have hT : ∀ Q, EPT K D Q = -(K.c - K.c3) * Q + (K.p + K.g2 - K.c3) * (∫ x, min x Q ∂D)
      + (-K.g2 * (∫ x, x ∂D)) := fun Q => by rw [PRSubopt180.EPT_eq K D hX Q]; ring
  have hleft : ∀ Q, IsOptimalOrder (EPT K D) Q → 0 < Q →
      K.c - K.c3 ≤ (K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D Q) := by
    intro Q hQ hQ0
    have hsub : Set.Ico 0 Q ⊆
        {t | K.c - K.c3 ≤ (K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D t)} := by
      rintro Q1 ⟨h0, h1⟩
      have hle := (isMaxOn_iff.1 hQ.2) Q1 (Set.mem_Ici.2 h0)
      have hu := PRSubopt180.nv_upper D hX hA.le (EPT K D) h1.le (hT Q1) (hT Q)
      by_contra hneg
      simp only [Set.mem_ofPred_eq, not_le] at hneg
      have : (Q - Q1) * ((K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D Q1)
          - (K.c - K.c3)) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      linarith
    have hcl : IsClosed
        {t | K.c - K.c3 ≤ (K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D t)} :=
      isClosed_le continuous_const (continuous_const.mul (continuous_const.sub hcont))
    exact (hcl.closure_subset_iff.2 hsub) (by rw [closure_Ico hQ0.ne]; exact ⟨hQ0.le, le_rfl⟩)
  have hright : ∀ Q, IsOptimalOrder (EPT K D) Q →
      (K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D Q) ≤ K.c - K.c3 := by
    intro Q hQ
    have hsub : Set.Ioi Q ⊆
        {t | (K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D t) ≤ K.c - K.c3} := by
      intro Q2 h1
      have h1 : Q < Q2 := h1
      have hle := (isMaxOn_iff.1 hQ.2) Q2 (Set.mem_Ici.2 (by linarith [hQ.1]))
      have hl := PRSubopt180.nv_lower D hX hA.le (EPT K D) h1.le (hT Q) (hT Q2)
      by_contra hneg
      simp only [Set.mem_ofPred_eq, not_le] at hneg
      have : 0 < (Q2 - Q) * ((K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D Q2)
          - (K.c - K.c3)) :=
        mul_pos (by linarith) (by linarith)
      linarith
    have hcl : IsClosed
        {t | (K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D t) ≤ K.c - K.c3} :=
      isClosed_le (continuous_const.mul (continuous_const.sub hcont)) continuous_const
    exact (hcl.closure_subset_iff.2 hsub) (by rw [closure_Ioi]; exact Set.mem_Ici.2 le_rfl)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (K.p + K.g2 - K.c) / (K.p + K.g2 - K.c3) := ⟨_, rfl⟩
    have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) hA
    have hθ1 : θ < 1 := by rw [hθ]; exact (div_lt_one hA).2 (by linarith)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      ((tendsto_order.1 (ProbabilityTheory.tendsto_cdf_atTop (μ := D))).1 θ hθ1)
    have hTN := hN (max N 0) (le_max_left _ _)
    obtain ⟨Qs, ⟨hQs0, -⟩, hQs⟩ := intermediate_value_Icc (le_max_right N 0) hcont.continuousOn
      (show θ ∈ Set.Icc (ProbabilityTheory.cdf D 0) (ProbabilityTheory.cdf D (max N 0)) from
        ⟨by rw [hF0]; exact hθ0.le, hTN.le⟩)
    have hkey : (K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D Qs) = K.c - K.c3 := by
      have hA' := hA.ne'
      rw [hQs, hθ]
      field_simp
      ring
    refine ⟨Qs, hQs0, isMaxOn_iff.2 fun Q hQ => ?_⟩
    have hQ : 0 ≤ Q := hQ
    rcases le_total Qs Q with h | h
    · have hu := PRSubopt180.nv_upper D hX hA.le (EPT K D) h (hT Qs) (hT Q)
      rw [hkey, sub_self, mul_zero] at hu
      linarith
    · have hl := PRSubopt180.nv_lower D hX hA.le (EPT K D) h (hT Q) (hT Qs)
      rw [hkey, sub_self, mul_zero] at hl
      linarith
  · intro Q hQ hR
    have hF1 : ProbabilityTheory.cdf D Q < 1 := by
      rcases hQ.1.eq_or_lt with h0 | h0
      · rw [← h0, hF0]; norm_num
      · have := hleft Q hQ h0
        by_contra hne
        push Not at hne
        have : 1 - ProbabilityTheory.cdf D Q ≤ 0 := by linarith
        nlinarith
    have hev : ∀ᶠ t in nhds Q, ProbabilityTheory.cdf D t < 1 :=
      hcont.continuousAt.eventually (gt_mem_nhds hF1)
    obtain ⟨Q2, hQ2, hQ2gt⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi Q))).and
      (self_mem_nhdsWithin (s := Set.Ioi Q))).exists
    have hQ2gt : Q < Q2 := hQ2gt
    have hA1 : 0 ≤ K.p - c1 + K.g := by linarith
    have hl := PRSubopt180.nv_lower D hX hA1 (EPR K c1 c1 1 D) (B := 0)
      (C := -K.g * (∫ x, x ∂D)) hQ2gt.le
      (by rw [PRSubopt180.EPR1_eq K c1 D hD hQ.1]; ring)
      (by rw [PRSubopt180.EPR1_eq K c1 D hD (by linarith [hQ.1])]; ring)
    have hle := (isMaxOn_iff.1 hR.2) Q2 (Set.mem_Ici.2 (by linarith [hQ.1]))
    have hpos : 0 < (Q2 - Q) * ((K.p - c1 + K.g) * (1 - ProbabilityTheory.cdf D Q2) - 0) := by
      apply mul_pos (by linarith)
      have h3 : 0 < 1 - ProbabilityTheory.cdf D Q2 := by linarith
      have h4 : 0 < K.p - c1 + K.g := by linarith
      nlinarith
    linarith
  · intro c2 Q hQ hR
    have hr := hright Q hQ
    have hQpos : 0 < Q := by
      rcases hQ.1.eq_or_lt with h0 | h0
      · rw [← h0, hF0, sub_zero, mul_one] at hr; linarith
      · exact h0
    have hle1 := ProbabilityTheory.cdf_le_one (μ := D) Q
    have hA0 : 0 < K.p + K.g - K.c3 := by linarith
    have hstrict : (K.p + K.g - K.c3) * (1 - ProbabilityTheory.cdf D Q) < c1 - K.c3 := by
      have : (K.p + K.g - K.c3) * (1 - ProbabilityTheory.cdf D Q)
          ≤ (K.p + K.g2 - K.c3) * (1 - ProbabilityTheory.cdf D Q) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    have hcf : Continuous fun t => (K.p + K.g - K.c3) * (1 - ProbabilityTheory.cdf D t) :=
      continuous_const.mul (continuous_const.sub hcont)
    have hev : ∀ᶠ t in nhds Q, (K.p + K.g - K.c3) * (1 - ProbabilityTheory.cdf D t) < c1 - K.c3 :=
      hcf.continuousAt.eventually (gt_mem_nhds hstrict)
    have hev0 : ∀ᶠ t in nhds Q, 0 < t := lt_mem_nhds hQpos
    obtain ⟨Q1, ⟨hQ1, hQ10⟩, hQ1lt⟩ :=
      (((hev.and hev0).filter_mono (nhdsWithin_le_nhds (s := Set.Iio Q))).and
        (self_mem_nhdsWithin (s := Set.Iio Q))).exists
    have hQ1lt : Q1 < Q := hQ1lt
    have hu := PRSubopt180.nv_upper D hX hA0.le (EPR K c1 c2 0 D) (B := c1 - K.c3)
      (C := -K.g * (∫ x, x ∂D)) hQ1lt.le
      (by rw [PRSubopt180.EPR0_eq K c1 c2 D hX Q1]; ring)
      (by rw [PRSubopt180.EPR0_eq K c1 c2 D hX Q]; ring)
    have hle := (isMaxOn_iff.1 hR.2) Q1 (Set.mem_Ici.2 hQ10.le)
    have : (Q - Q1) * ((K.p + K.g - K.c3) * (1 - ProbabilityTheory.cdf D Q1) - (c1 - K.c3)) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
