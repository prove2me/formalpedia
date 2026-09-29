-- Prove2me | solution 1 for SupportVectorMachines.Regression.lemma_9_2_concentration_of_hilbert_space_valued_means
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:34:38.529238+00:00
-- url     : https://prove2.me/submissions/a4267de7-7a5a-4b65-80b9-2c71b6e3a4c0

import Mathlib

open MeasureTheory TopologicalSpace

namespace SupportVectorMachines.Regression

theorem aux_l92_near {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (q : ℝ) (hq : 1 < q) (s z : H) (hs : s ≠ 0) (hz : 2 * q * ‖z‖ ≤ ‖s‖) :
    ‖s + z‖ ^ q ≤ ‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s z
      + (q / 2 + 9 * q ^ 2 / 4) * (‖s‖ ^ (q - 2) * ‖z‖ ^ 2) := by
  have hn2 : ‖s + z‖ ^ 2 = ‖s‖ ^ 2 + 2 * inner ℝ s z + ‖z‖ ^ 2 := norm_add_sq_real s z
  have hip : |inner ℝ s z| ≤ ‖s‖ * ‖z‖ := abs_real_inner_le_norm s z
  have ha : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hb : 0 ≤ ‖z‖ := norm_nonneg _
  set a := ‖s‖ with ha_def
  set b := ‖z‖ with hb_def
  set ip := inner ℝ s z with hip_def
  have hba : b ≤ a := by nlinarith
  have hB : |2 * ip + b ^ 2| ≤ 3 * a * b := by
    rw [abs_le] at hip ⊢; constructor <;> nlinarith
  have ha2 : 0 < a ^ 2 := by positivity
  set t := (2 * ip + b ^ 2) / a ^ 2 with ht_def
  have h1t : ‖s + z‖ ^ 2 = a ^ 2 * (1 + t) := by
    rw [hn2, ht_def]; field_simp; ring
  have h1t' : 0 ≤ 1 + t := by
    have h0 : 0 ≤ ‖s + z‖ ^ 2 := sq_nonneg _
    rw [h1t] at h0
    exact nonneg_of_mul_nonneg_right (by linarith) ha2
  set u := t * (q / 2) with hu_def
  have hu : |u| ≤ 1 := by
    rw [hu_def, ht_def, abs_mul, abs_div, abs_of_pos ha2, abs_of_pos (by linarith : (0:ℝ) < q / 2),
      div_mul_eq_mul_div, div_le_one ha2]
    have h1 := mul_le_mul_of_nonneg_right hB (by linarith : (0:ℝ) ≤ q / 2)
    have h2 := mul_le_mul_of_nonneg_left hz ha.le
    nlinarith
  have hpow : ‖s + z‖ ^ q = a ^ q * (1 + t) ^ (q / 2) := by
    have : ‖s + z‖ ^ q = (‖s + z‖ ^ 2) ^ (q / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num [show 2 * (q / 2) = q by ring]
    rw [this, h1t, Real.mul_rpow ha2.le h1t']
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num [show 2 * (q / 2) = q by ring]
  have hexp : (1 + t) ^ (q / 2) ≤ 1 + u + u ^ 2 := by
    calc (1 + t) ^ (q / 2) ≤ (Real.exp t) ^ (q / 2) :=
          Real.rpow_le_rpow h1t' (by linarith [Real.add_one_le_exp t]) (by linarith)
      _ = Real.exp u := by rw [← Real.exp_mul]
      _ ≤ 1 + u + u ^ 2 := by
          have := Real.abs_exp_sub_one_sub_id_le hu
          rw [abs_le] at this; linarith [this.2]
  have hA : a ^ q = a ^ (q - 2) * a ^ 2 := by
    rw [Real.rpow_sub ha, Real.rpow_two]; field_simp
  have hApos : 0 < a ^ (q - 2) := Real.rpow_pos_of_pos ha _
  have key : a ^ 2 * (1 + u + u ^ 2) ≤ a ^ 2 + q * ip + (q / 2 + 9 * q ^ 2 / 4) * b ^ 2 := by
    have e1 : a ^ 2 * u = q * ip + q / 2 * b ^ 2 := by
      rw [hu_def, ht_def]; field_simp
    have e2 : a ^ 2 * u ^ 2 ≤ 9 * q ^ 2 / 4 * b ^ 2 := by
      have e3 : a ^ 2 * u ^ 2 = ((2 * ip + b ^ 2) * (q / 2)) ^ 2 / a ^ 2 := by
        rw [hu_def, ht_def]; field_simp
      rw [e3, div_le_iff₀ ha2]
      have e4 : (2 * ip + b ^ 2) ^ 2 ≤ (3 * a * b) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB 2
      nlinarith
    nlinarith
  calc ‖s + z‖ ^ q = a ^ q * (1 + t) ^ (q / 2) := hpow
    _ ≤ a ^ q * (1 + u + u ^ 2) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = a ^ (q - 2) * (a ^ 2 * (1 + u + u ^ 2)) := by rw [hA]; ring
    _ ≤ a ^ (q - 2) * (a ^ 2 + q * ip + (q / 2 + 9 * q ^ 2 / 4) * b ^ 2) :=
        mul_le_mul_of_nonneg_left key hApos.le
    _ = _ := by rw [hA]; ring

theorem aux_l92_far {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (q : ℝ) (hq : 1 < q) (s z : H) (hz : ‖s‖ ≤ 2 * q * ‖z‖) :
    ‖s + z‖ ^ q ≤ ‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s z
      + ((2 * q + 1) ^ q + q * (2 * q) ^ (q - 1)) * ‖z‖ ^ q := by
  have hip : |inner ℝ s z| ≤ ‖s‖ * ‖z‖ := abs_real_inner_le_norm s z
  have hb : 0 ≤ ‖z‖ := norm_nonneg _
  have hsz : ‖s + z‖ ≤ ‖s‖ + ‖z‖ := norm_add_le _ _
  have hs0 : s = 0 → inner ℝ s z = 0 := fun h => by simp [h]
  have ha0 : 0 ≤ ‖s‖ := norm_nonneg _
  set a := ‖s‖ with ha_def
  set b := ‖z‖ with hb_def
  set ip := inner ℝ s z with hip_def
  have h1 : ‖s + z‖ ^ q ≤ (2 * q + 1) ^ q * b ^ q := by
    rw [← Real.mul_rpow (by linarith) hb]
    apply Real.rpow_le_rpow (norm_nonneg _) _ (by linarith)
    nlinarith
  have h2 : -(q * ((2 * q) ^ (q - 1) * b ^ q)) ≤ q * a ^ (q - 2) * ip := by
    rcases eq_or_lt_of_le ha0 with h | h
    · have : s = 0 := norm_eq_zero.mp h.symm
      rw [hs0 this, mul_zero]
      have : 0 ≤ (2 * q) ^ (q - 1) * b ^ q := by positivity
      nlinarith
    · have hbpos : 0 < b := by nlinarith
      have habs : |a ^ (q - 2) * ip| ≤ (2 * q) ^ (q - 1) * b ^ q := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos h _)]
        calc a ^ (q - 2) * |ip| ≤ a ^ (q - 2) * (a * b) :=
              mul_le_mul_of_nonneg_left hip (by positivity)
          _ = a ^ (q - 2 + 1) * b := by rw [Real.rpow_add_one h.ne']; ring
          _ = a ^ (q - 1) * b := by ring_nf
          _ ≤ (2 * q * b) ^ (q - 1) * b := by
              gcongr
          _ = (2 * q) ^ (q - 1) * b ^ (q - 1 + 1) := by
              rw [Real.mul_rpow (by positivity) hbpos.le, Real.rpow_add_one hbpos.ne']; ring
          _ = (2 * q) ^ (q - 1) * b ^ q := by ring_nf
      have := neg_abs_le (a ^ (q - 2) * ip)
      have hq0 : 0 < q := by linarith
      nlinarith
  have h3 : 0 ≤ a ^ q := by positivity
  nlinarith

theorem aux_l92_decomp {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (X : Z → H) (hX : Measurable X) (F : H → ENNReal) (hF : Measurable F) (n : ℕ) :
    ∫⁻ w, F (∑ i, X (w i)) ∂(Measure.pi fun _ : Fin (n+1) => P) =
      ∫⁻ w, ∫⁻ y, F (X y + ∑ i, X (w i)) ∂P ∂(Measure.pi fun _ : Fin n => P) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => P) 0).symm
  have hmeas : Measurable fun w : Fin (n+1) → Z => F (∑ i, X (w i)) := by
    apply hF.comp
    exact Finset.measurable_sum _ fun i _ => hX.comp (measurable_pi_apply i)
  rw [← hmp.lintegral_comp hmeas]
  rw [lintegral_prod_symm]
  · congr 1
    ext w
    congr 1
    ext y
    congr 1
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.sum_univ_succ]
  · exact (hmeas.comp (MeasurableEquiv.measurable _)).aemeasurable

/-- the constant in the pointwise inequality -/
noncomputable def aux_l92_C (q : ℝ) : ℝ :=
  (q / 2 + 9 * q ^ 2 / 4) + ((2 * q + 1) ^ q + q * (2 * q) ^ (q - 1))

theorem aux_l92_C_nonneg (q : ℝ) (hq : 1 < q) : 0 ≤ aux_l92_C q := by
  unfold aux_l92_C
  have : 0 < q := by linarith
  positivity

theorem aux_l92_pt1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (q : ℝ) (hq : 1 < q) (s z : H) :
    ‖s + z‖ ^ q ≤ ‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s z
      + aux_l92_C q * (‖s‖ ^ (q - 2) * ‖z‖ ^ 2 + ‖z‖ ^ q) := by
  have hq0 : 0 < q := by linarith
  have hX : 0 ≤ ‖s‖ ^ (q - 2) * ‖z‖ ^ 2 := by positivity
  have hY : 0 ≤ ‖z‖ ^ q := by positivity
  have hCn : 0 ≤ q / 2 + 9 * q ^ 2 / 4 := by positivity
  have hCf : 0 ≤ (2 * q + 1) ^ q + q * (2 * q) ^ (q - 1) := by positivity
  unfold aux_l92_C
  by_cases h : s ≠ 0 ∧ 2 * q * ‖z‖ ≤ ‖s‖
  · have := aux_l92_near q hq s z h.1 h.2
    nlinarith [mul_nonneg hCn hY, mul_nonneg hCf hX, mul_nonneg hCf hY]
  · have hfar : ‖s‖ ≤ 2 * q * ‖z‖ := by
      by_cases hs : s = 0
      · rw [hs, norm_zero]; positivity
      · have : ¬ (2 * q * ‖z‖ ≤ ‖s‖) := fun h' => h ⟨hs, h'⟩
        linarith
    have := aux_l92_far q hq s z hfar
    nlinarith [mul_nonneg hCn hY, mul_nonneg hCf hX, mul_nonneg hCn hX]

theorem aux_l92_pt2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (q : ℝ) (hq : 1 < q) (hq2 : q ≤ 2) (s z : H) :
    ‖s + z‖ ^ q ≤ ‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s z + aux_l92_C q * ‖z‖ ^ q := by
  have hq0 : 0 < q := by linarith
  have hX : 0 ≤ ‖s‖ ^ (q - 2) * ‖z‖ ^ 2 := by positivity
  have hY : 0 ≤ ‖z‖ ^ q := by positivity
  have hCn : 0 ≤ q / 2 + 9 * q ^ 2 / 4 := by positivity
  have hCf : 0 ≤ (2 * q + 1) ^ q + q * (2 * q) ^ (q - 1) := by positivity
  unfold aux_l92_C
  by_cases h : s ≠ 0 ∧ 2 * q * ‖z‖ ≤ ‖s‖
  · have h1 := aux_l92_near q hq s z h.1 h.2
    have h2 : ‖s‖ ^ (q - 2) * ‖z‖ ^ 2 ≤ ‖z‖ ^ q := by
      rcases eq_or_lt_of_le (norm_nonneg z) with hb | hb
      · rw [← hb]; simp [Real.zero_rpow hq0.ne']
      · have hba : ‖z‖ ≤ ‖s‖ := by nlinarith
        have h3 : ‖s‖ ^ (q - 2) ≤ ‖z‖ ^ (q - 2) := Real.rpow_le_rpow_of_nonpos hb hba (by linarith)
        have h4 : ‖z‖ ^ (q - 2) * ‖z‖ ^ 2 = ‖z‖ ^ q := by
          rw [Real.rpow_sub hb, Real.rpow_two]; field_simp
        calc ‖s‖ ^ (q - 2) * ‖z‖ ^ 2 ≤ ‖z‖ ^ (q - 2) * ‖z‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = _ := h4
    nlinarith [mul_nonneg hCf hY, mul_le_mul_of_nonneg_left h2 hCn]
  · have hfar : ‖s‖ ≤ 2 * q * ‖z‖ := by
      by_cases hs : s = 0
      · rw [hs, norm_zero]; positivity
      · have : ¬ (2 * q * ‖z‖ ≤ ‖s‖) := fun h' => h ⟨hs, h'⟩
        linarith
    have := aux_l92_far q hq s z hfar
    nlinarith [mul_nonneg hCn hY]

theorem aux_l92_step2 {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (q : ℝ) (hq : 1 < q) (hq2 : q ≤ 2) (X : Z → H) (hXi : Integrable X P)
    (hX0 : ∫ y, X y ∂P = 0) (hXq : Integrable (fun y => ‖X y‖ ^ q) P) (s : H) :
    ∫⁻ y, ENNReal.ofReal (‖X y + s‖ ^ q) ∂P ≤
      ENNReal.ofReal (‖s‖ ^ q + aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by
  have hR : ∀ y, ‖X y + s‖ ^ q ≤ ‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)
      + aux_l92_C q * ‖X y‖ ^ q := fun y => by
    rw [add_comm]; exact aux_l92_pt2 q hq hq2 s (X y)
  have h1 : Integrable (fun _ : Z => ‖s‖ ^ q) P := integrable_const _
  have h2 : Integrable (fun y => q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)) P :=
    (hXi.const_inner s).const_mul _
  have h3 : Integrable (fun y => aux_l92_C q * ‖X y‖ ^ q) P := hXq.const_mul _
  have h12 : Integrable (fun y => ‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)) P := h1.add h2
  calc ∫⁻ y, ENNReal.ofReal (‖X y + s‖ ^ q) ∂P
      ≤ ∫⁻ y, ENNReal.ofReal (‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)
          + aux_l92_C q * ‖X y‖ ^ q) ∂P :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hR y)
    _ = ENNReal.ofReal (∫ y, (‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)
          + aux_l92_C q * ‖X y‖ ^ q) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal ((h1.add h2).add h3)
          (ae_of_all _ fun y => le_trans (by positivity) (hR y))).symm
    _ = _ := by
        congr 1
        rw [integral_add h12 h3, integral_add h1 h2, integral_const, integral_const_mul,
          integral_const_mul, integral_inner hXi, hX0, inner_zero_right]
        simp

theorem aux_l92_stepq {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (q : ℝ) (hq : 2 < q) (X : Z → H) (hXi : Integrable X P)
    (hX0 : ∫ y, X y ∂P = 0) (hXq : Integrable (fun y => ‖X y‖ ^ q) P)
    (hX2 : Integrable (fun y => ‖X y‖ ^ 2) P) (s : H) :
    ∫⁻ y, ENNReal.ofReal (‖X y + s‖ ^ q) ∂P ≤
      ENNReal.ofReal (‖s‖ ^ q)
        + ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ 2 ∂P) * ENNReal.ofReal (‖s‖ ^ (q - 2))
        + ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by
  have hq1 : 1 < q := by linarith
  have hC := aux_l92_C_nonneg q hq1
  have hR : ∀ y, ‖X y + s‖ ^ q ≤ ‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)
      + aux_l92_C q * (‖s‖ ^ (q - 2) * ‖X y‖ ^ 2 + ‖X y‖ ^ q) := fun y => by
    rw [add_comm]; exact aux_l92_pt1 q hq1 s (X y)
  have h1 : Integrable (fun _ : Z => ‖s‖ ^ q) P := integrable_const _
  have h2 : Integrable (fun y => q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)) P :=
    (hXi.const_inner s).const_mul _
  have h3 : Integrable (fun y => aux_l92_C q * (‖s‖ ^ (q - 2) * ‖X y‖ ^ 2 + ‖X y‖ ^ q)) P :=
    ((hX2.const_mul _).add hXq).const_mul _
  have h12 : Integrable (fun y => ‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)) P := h1.add h2
  have h4 : Integrable (fun y => ‖s‖ ^ (q - 2) * ‖X y‖ ^ 2) P := hX2.const_mul _
  have hσ : 0 ≤ ∫ y, ‖X y‖ ^ 2 ∂P := integral_nonneg fun y => by positivity
  have hm : 0 ≤ ∫ y, ‖X y‖ ^ q ∂P := integral_nonneg fun y => by positivity
  calc ∫⁻ y, ENNReal.ofReal (‖X y + s‖ ^ q) ∂P
      ≤ ∫⁻ y, ENNReal.ofReal (‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)
          + aux_l92_C q * (‖s‖ ^ (q - 2) * ‖X y‖ ^ 2 + ‖X y‖ ^ q)) ∂P :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hR y)
    _ = ENNReal.ofReal (∫ y, (‖s‖ ^ q + q * ‖s‖ ^ (q - 2) * inner ℝ s (X y)
          + aux_l92_C q * (‖s‖ ^ (q - 2) * ‖X y‖ ^ 2 + ‖X y‖ ^ q)) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal ((h1.add h2).add h3)
          (ae_of_all _ fun y => le_trans (by positivity) (hR y))).symm
    _ = ENNReal.ofReal (‖s‖ ^ q + (aux_l92_C q * ∫ y, ‖X y‖ ^ 2 ∂P) * ‖s‖ ^ (q - 2)
          + aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by
        congr 1
        rw [integral_add h12 h3, integral_add h1 h2, integral_const, integral_const_mul,
          integral_const_mul, integral_inner hXi, hX0, inner_zero_right,
          integral_add h4 hXq, integral_const_mul]
        simp; ring
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]

theorem aux_l92_jensen {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] (S : Ω → H) (hS : AEStronglyMeasurable S μ)
    (q : ℝ) (hq : 2 < q) :
    ∫⁻ w, ENNReal.ofReal (‖S w‖ ^ (q - 2)) ∂μ ≤
      (∫⁻ w, ENNReal.ofReal (‖S w‖ ^ q) ∂μ) ^ ((q - 2) / q) := by
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le (by linarith : 0 < q - 2) (by linarith : q - 2 ≤ q)
    μ hS
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm] at h
  have conv : ∀ p : ℝ, 0 ≤ p → ∀ w, ‖S w‖ₑ ^ p = ENNReal.ofReal (‖S w‖ ^ p) := fun p hp w => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp]
  simp_rw [conv (q - 2) (by linarith), conv q (by linarith)] at h
  have h2 := ENNReal.rpow_le_rpow h (by linarith : 0 ≤ q - 2)
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  have hq2 : q - 2 ≠ 0 := by linarith
  rw [show 1 / (q - 2) * (q - 2) = 1 by field_simp, ENNReal.rpow_one,
    show 1 / q * (q - 2) = (q - 2) / q by ring] at h2
  exact h2

theorem aux_l92_realrec (p : ℝ) (hp : 1 < p) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    (α + β + 1) ^ p * (n : ℝ) ^ p + α * ((α + β + 1) ^ p * (n : ℝ) ^ p) ^ (1 - 1 / p) + β ≤
      (α + β + 1) ^ p * ((n : ℝ) + 1) ^ p := by
  set M := α + β + 1 with hM
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : M ^ p * (n : ℝ) ^ p = (M * n) ^ p := (Real.mul_rpow hM0.le hn0).symm
  have e2 : ((M * n) ^ p) ^ (1 - 1 / p) = (M * n) ^ (p - 1) := by
    rw [← Real.rpow_mul (by positivity)]; congr 1; field_simp
  have e3 : M ^ p * ((n : ℝ) + 1) ^ p = (M * n + M) ^ p := by
    rw [← Real.mul_rpow hM0.le (by positivity)]; ring_nf
  rw [e1, e2, e3]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have hp0 : p ≠ 0 := by linarith
    have hp1 : p - 1 ≠ 0 := by linarith
    simp only [Nat.cast_zero, mul_zero, zero_add, Real.zero_rpow hp0, Real.zero_rpow hp1]
    have : M ≤ M ^ p := by
      calc M = M ^ (1 : ℝ) := (Real.rpow_one M).symm
        _ ≤ M ^ p := Real.rpow_le_rpow_of_exponent_le hM1 hp.le
    linarith
  · set y := M * n with hy
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hy1 : M ≤ y := by rw [hy]; nlinarith
    have hy0 : 0 < y := by linarith
    have hb := one_add_mul_self_le_rpow_one_add (s := M / y) (by
      have : 0 ≤ M / y := by positivity
      linarith) hp.le
    have e4 : (y + M) ^ p = y ^ p * (1 + M / y) ^ p := by
      rw [← Real.mul_rpow hy0.le (by positivity)]; congr 1; field_simp
    have e5 : y ^ p * (1 + p * (M / y)) = y ^ p + p * M * y ^ (p - 1) := by
      rw [Real.rpow_sub_one hy0.ne']; field_simp
    have hyp : 1 ≤ y ^ (p - 1) := Real.one_le_rpow (by linarith) (by linarith)
    have hyp0 : 0 ≤ y ^ p := by positivity
    have h6 : y ^ p + p * M * y ^ (p - 1) ≤ (y + M) ^ p := by
      rw [e4, ← e5]; exact mul_le_mul_of_nonneg_left hb hyp0
    nlinarith [mul_le_mul_of_nonneg_right hp.le (by positivity : (0:ℝ) ≤ M * y ^ (p - 1))]


theorem aux_l92_ennrec (v : ℕ → ENNReal) (p : ℝ) (hp : 1 < p) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h0 : v 0 = 0)
    (hrec : ∀ n, v (n + 1) ≤ v n + ENNReal.ofReal α * v n ^ (1 - 1 / p) + ENNReal.ofReal β) :
    ∀ n : ℕ, v n ≤ ENNReal.ofReal ((α + β + 1) ^ p * (n : ℝ) ^ p) := by
  intro n
  induction n with
  | zero => rw [h0]; exact zero_le
  | succ n ih =>
    have hθ : 0 ≤ 1 - 1 / p := by
      have : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
      linarith
    have hK : 0 ≤ (α + β + 1) ^ p * (n : ℝ) ^ p := by positivity
    calc v (n + 1) ≤ v n + ENNReal.ofReal α * v n ^ (1 - 1 / p) + ENNReal.ofReal β := hrec n
      _ ≤ ENNReal.ofReal ((α + β + 1) ^ p * (n : ℝ) ^ p) + ENNReal.ofReal α *
            (ENNReal.ofReal ((α + β + 1) ^ p * (n : ℝ) ^ p)) ^ (1 - 1 / p) + ENNReal.ofReal β := by
          gcongr
      _ = ENNReal.ofReal ((α + β + 1) ^ p * (n : ℝ) ^ p +
            α * ((α + β + 1) ^ p * (n : ℝ) ^ p) ^ (1 - 1 / p) + β) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hK hθ, ← ENNReal.ofReal_mul hα,
            ← ENNReal.ofReal_add hK (by positivity), ← ENNReal.ofReal_add (by positivity) hβ]
      _ ≤ ENNReal.ofReal ((α + β + 1) ^ p * ((n + 1 : ℕ) : ℝ) ^ p) := by
          apply ENNReal.ofReal_le_ofReal
          push_cast
          exact aux_l92_realrec p hp α β hα hβ n

theorem aux_l92_mom2 {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (q : ℝ) (hq : 1 < q) (hq2 : q ≤ 2) (X : Z → H) (hXm : Measurable X) (hXi : Integrable X P)
    (hX0 : ∫ y, X y ∂P = 0) (hXq : Integrable (fun y => ‖X y‖ ^ q) P) (n : ℕ) :
    ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P) ≤
      n * ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by
  have hF : Measurable fun x : H => ENNReal.ofReal (‖x‖ ^ q) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const q)
  have hB : 0 ≤ aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P :=
    mul_nonneg (aux_l92_C_nonneg q hq) (integral_nonneg fun y => by positivity)
  induction n with
  | zero => simp [Real.zero_rpow (by linarith : q ≠ 0)]
  | succ n ih =>
    rw [aux_l92_decomp P X hXm _ hF n]
    calc ∫⁻ w, ∫⁻ y, ENNReal.ofReal (‖X y + ∑ i, X (w i)‖ ^ q) ∂P ∂(Measure.pi fun _ : Fin n => P)
        ≤ ∫⁻ w, (ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) +
            ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P)) ∂(Measure.pi fun _ : Fin n => P) := by
          apply lintegral_mono; intro w
          refine (aux_l92_step2 P q hq hq2 X hXi hX0 hXq _).trans ?_
          rw [ENNReal.ofReal_add (by positivity) hB]
      _ = ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P) +
            ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ n * ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) +
            ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by gcongr
      _ = ((n + 1 : ℕ) : ENNReal) * ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by
          push_cast; ring

theorem aux_l92_momq {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (q : ℝ) (hq : 2 < q) (X : Z → H) (hXm : Measurable X) (hXi : Integrable X P)
    (hX0 : ∫ y, X y ∂P = 0) (hXq : Integrable (fun y => ‖X y‖ ^ q) P)
    (hX2 : Integrable (fun y => ‖X y‖ ^ 2) P) (n : ℕ) :
    ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P) ≤
      ENNReal.ofReal ((aux_l92_C q * ∫ y, ‖X y‖ ^ 2 ∂P + aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P + 1)
        ^ (q / 2) * (n : ℝ) ^ (q / 2)) := by
  have hq1 : 1 < q := by linarith
  have hC := aux_l92_C_nonneg q hq1
  have hF : ∀ p : ℝ, Measurable fun x : H => ENNReal.ofReal (‖x‖ ^ p) := fun p =>
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const p)
  have hσ : 0 ≤ ∫ y, ‖X y‖ ^ 2 ∂P := integral_nonneg fun y => by positivity
  have hm : 0 ≤ ∫ y, ‖X y‖ ^ q ∂P := integral_nonneg fun y => by positivity
  refine aux_l92_ennrec
    (fun n => ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P))
    (q / 2) (by linarith) _ _ (mul_nonneg hC hσ) (mul_nonneg hC hm) ?_ ?_ n
  · simp [Real.zero_rpow (by linarith : q ≠ 0)]
  · intro n
    have hSm : Measurable fun w : Fin n → Z => ∑ i, X (w i) :=
      Finset.measurable_sum _ fun i _ => hXm.comp (measurable_pi_apply i)
    have hS1 : Measurable fun w : Fin n → Z => ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) :=
      (hF q).comp hSm
    have hS2 : Measurable fun w : Fin n → Z => ENNReal.ofReal (‖∑ i, X (w i)‖ ^ (q - 2)) :=
      (hF (q - 2)).comp hSm
    rw [aux_l92_decomp P X hXm _ (hF q) n]
    calc ∫⁻ w, ∫⁻ y, ENNReal.ofReal (‖X y + ∑ i, X (w i)‖ ^ q) ∂P ∂(Measure.pi fun _ : Fin n => P)
        ≤ ∫⁻ w, (ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q)
            + ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ 2 ∂P)
              * ENNReal.ofReal (‖∑ i, X (w i)‖ ^ (q - 2))
            + ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P)) ∂(Measure.pi fun _ : Fin n => P) :=
          lintegral_mono fun w => aux_l92_stepq P q hq X hXi hX0 hXq hX2 _
      _ = ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P)
            + ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ 2 ∂P)
              * ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ (q - 2)) ∂(Measure.pi fun _ : Fin n => P)
            + ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left hS1,
            lintegral_const_mul _ hS2, lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P)
            + ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ 2 ∂P)
              * (∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P))
                ^ (1 - 1 / (q / 2))
            + ENNReal.ofReal (aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P) := by
          gcongr
          rw [show 1 - 1 / (q / 2) = (q - 2) / q by field_simp]
          exact aux_l92_jensen _ _ hSm.aestronglyMeasurable q hq

theorem aux_l92_zero {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]
    (q : ℝ) (hq : 1 < q) (X : Z → H) (hXm : Measurable X) (hXz : X =ᵐ[P] 0) (n : ℕ) :
    ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P) = 0 := by
  have hF : Measurable fun x : H => ENNReal.ofReal (‖x‖ ^ q) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const q)
  induction n with
  | zero => simp [Real.zero_rpow (by linarith : q ≠ 0)]
  | succ n ih =>
    rw [aux_l92_decomp P X hXm _ hF n]
    have h : ∀ w : Fin n → Z, ∫⁻ y, ENNReal.ofReal (‖X y + ∑ i, X (w i)‖ ^ q) ∂P =
        ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) := fun w => by
      rw [lintegral_congr_ae (hXz.mono fun y hy => by
        show ENNReal.ofReal (‖X y + ∑ i, X (w i)‖ ^ q) = ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q)
        rw [hy]; simp)]
      simp
    simp_rw [h]; exact ih

theorem aux_l92_markov {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (g : Z → H) (hg : Measurable g) (μg : H) (q : ℝ) (hq : 1 < q) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n => P) {z | ε ≤ ‖(n : ℝ)⁻¹ • (∑ i, g (z i)) - μg‖} ≤
      (∫⁻ w, ENNReal.ofReal (‖∑ i, (g (w i) - μg)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P)) /
        ENNReal.ofReal (((n : ℝ) * ε) ^ q) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < ((n : ℝ) * ε) ^ q := Real.rpow_pos_of_pos (by positivity) _
  refine le_trans (measure_mono ?_) (meas_ge_le_lintegral_div ?_ ?_ ?_)
  · intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    have e : (n : ℝ)⁻¹ • (∑ i, g (z i)) - μg = (n : ℝ)⁻¹ • ∑ i, (g (z i) - μg) := by
      rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hnpos.ne', one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnpos, ← div_eq_inv_mul,
      le_div_iff₀ hnpos] at hz
    linarith
  · exact (ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun i _ =>
      (hg.comp (measurable_pi_apply i)).sub_const _).norm.pow_const q)).aemeasurable
  · exact (ENNReal.ofReal_pos.mpr ht).ne'
  · exact ENNReal.ofReal_ne_top

end SupportVectorMachines.Regression

open SupportVectorMachines.Regression MeasureTheory TopologicalSpace

theorem solution
    {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SeparableSpace H]
    (g : Z → H) (hg : Measurable g)
    (q : ℝ) (hq : 1 < q) (hgInt : Integrable (fun z => ‖g z‖ ^ q) P) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
      (Measure.pi (fun _ : Fin n => P))
          {z : Fin n → Z | ε ≤ ‖(n : ℝ)⁻¹ • (∑ i, g (z i)) - ∫ z', g z' ∂P‖} ≤
        ENNReal.ofReal
          (c * ((∫ z, ‖g z‖ ^ q ∂P) ^ (1 / q) /
              (ε * (n : ℝ) ^ (min (1 / 2 : ℝ) (1 - 1 / q)))) ^ q) := by
  have hq0 : 0 < q := by linarith
  set μg := ∫ z', g z' ∂P with hμg
  set X : Z → H := fun z => g z - μg with hX_def
  have hXm : Measurable X := hg.sub_const _
  have hgm : MemLp g (ENNReal.ofReal q) P := by
    rw [← integrable_norm_rpow_iff hg.aestronglyMeasurable (by simp [hq0]) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
    exact hgInt
  have hgi : Integrable g P :=
    hgm.integrable (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le)
  have hXmem : MemLp X (ENNReal.ofReal q) P := hgm.sub (memLp_const μg)
  have hXi : Integrable X P := hgi.sub (integrable_const _)
  have hX0 : ∫ y, X y ∂P = 0 := by
    simp only [hX_def]
    rw [integral_sub hgi (integrable_const _), integral_const]
    simp [hμg]
  have hXq : Integrable (fun y => ‖X y‖ ^ q) P := by
    have := hXmem.integrable_norm_rpow (by simp [hq0]) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hq0.le] at this
  set qs := min (1 / 2 : ℝ) (1 - 1 / q) with hqs
  have hmom : ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      ∫⁻ w, ENNReal.ofReal (‖∑ i, X (w i)‖ ^ q) ∂(Measure.pi fun _ : Fin n => P) ≤
        ENNReal.ofReal (K * (n : ℝ) ^ (q - q * qs)) := by
    have hC := aux_l92_C_nonneg q hq
    have hβ : 0 ≤ aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P :=
      mul_nonneg hC (integral_nonneg fun y => by positivity)
    by_cases hq2 : q ≤ 2
    · have hr : q - q * qs = 1 := by
        have h1 : qs = 1 - 1 / q := by
          rw [hqs]; apply min_eq_right
          have : 1 / 2 ≤ 1 / q := one_div_le_one_div_of_le hq0 hq2
          linarith
        rw [h1]; field_simp; ring
      refine ⟨aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P + 1, by linarith, fun n => ?_⟩
      rw [hr, Real.rpow_one]
      refine (aux_l92_mom2 P q hq hq2 X hXm hXi hX0 hXq n).trans ?_
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      apply ENNReal.ofReal_le_ofReal
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    · push Not at hq2
      have hr : q - q * qs = q / 2 := by
        have h1 : qs = 1 / 2 := by
          rw [hqs]; apply min_eq_left
          have : 1 / q < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hq2
          linarith
        rw [h1]; ring
      have hX2 : Integrable (fun y => ‖X y‖ ^ 2) P := by
        have := integrable_norm_rpow_of_le hXm.aestronglyMeasurable (by norm_num : (0:ℝ) ≤ 2)
          hq0.le hq2.le hXq
        simpa [Real.rpow_two] using this
      have hα : 0 ≤ aux_l92_C q * ∫ y, ‖X y‖ ^ 2 ∂P :=
        mul_nonneg hC (integral_nonneg fun y => by positivity)
      refine ⟨(aux_l92_C q * ∫ y, ‖X y‖ ^ 2 ∂P + aux_l92_C q * ∫ y, ‖X y‖ ^ q ∂P + 1) ^ (q / 2),
        Real.rpow_pos_of_pos (by linarith) (q / 2), fun n => ?_⟩
      rw [hr]
      exact aux_l92_momq P q hq2 X hXm hXi hX0 hXq hX2 n
  obtain ⟨K, hK, hmom⟩ := hmom
  have hmark : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
      (Measure.pi fun _ : Fin n => P) {z | ε ≤ ‖(n : ℝ)⁻¹ • (∑ i, g (z i)) - μg‖} ≤
        ENNReal.ofReal (K * (n : ℝ) ^ (q - q * qs) / ((n : ℝ) * ε) ^ q) := by
    intro ε hε n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have ht : 0 < ((n : ℝ) * ε) ^ q := Real.rpow_pos_of_pos (by positivity) _
    refine (aux_l92_markov P g hg μg q hq ε hε n hn).trans ?_
    rw [ENNReal.ofReal_div_of_pos ht]
    gcongr
    exact hmom n
  by_cases hm0 : ∫ z, ‖g z‖ ^ q ∂P = 0
  · have hgz : ∀ᵐ z ∂P, g z = 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun z => by positivity) hgInt).mp hm0
      filter_upwards [this] with z hz
      simp only [Pi.zero_apply] at hz
      have := (Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)).mp hz
      exact norm_eq_zero.mp this.1
    have hμ0 : μg = 0 := by rw [hμg, integral_congr_ae hgz]; simp
    have hXz : X =ᵐ[P] 0 := by
      filter_upwards [hgz] with z hz
      simp [hX_def, hz, hμ0]
    refine ⟨1, one_pos, fun ε hε n hn => ?_⟩
    refine (aux_l92_markov P g hg μg q hq ε hε n hn).trans ?_
    have h0 := aux_l92_zero P q hq X hXm hXz n
    simp only [hX_def] at h0
    rw [h0, ENNReal.zero_div]
    exact zero_le
  · have hmpos : 0 < ∫ z, ‖g z‖ ^ q ∂P :=
      lt_of_le_of_ne (integral_nonneg fun z => by positivity) (Ne.symm hm0)
    refine ⟨K / ∫ z, ‖g z‖ ^ q ∂P, div_pos hK hmpos, fun ε hε n hn => ?_⟩
    refine (hmark ε hε n hn).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set m := ∫ z, ‖g z‖ ^ q ∂P
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hmpos.le,
      one_div_mul_cancel hq0.ne', Real.rpow_one, Real.mul_rpow hε.le (by positivity),
      ← Real.rpow_mul hnpos.le, Real.mul_rpow hnpos.le hε.le, Real.rpow_sub hnpos,
      mul_comm qs q]
    field_simp
