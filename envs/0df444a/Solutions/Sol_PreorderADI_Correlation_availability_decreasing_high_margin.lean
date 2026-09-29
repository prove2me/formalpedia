-- Prove2me | solution 1 for PreorderADI.Correlation.availability_decreasing_high_margin
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:01:28.860403+00:00
-- url     : https://prove2.me/submissions/486361b0-4706-475c-b04a-1529952a60b7

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

lemma aux_adm_Phi_strictMono : StrictMono stdNormalCdf := by
  intro a b hab
  unfold stdNormalCdf
  have h1 : ENNReal.ofReal (cdf (gaussianReal 0 1) a)
      < ENNReal.ofReal (cdf (gaussianReal 0 1) b) := by
    rw [ofReal_cdf, ofReal_cdf, ← Set.Iic_union_Ioc_eq_Iic hab.le,
      measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
    have hpos : gaussianReal 0 1 (Set.Ioc a b) ≠ 0 := by
      intro h
      have := gaussianReal_absolutelyContinuous' (0:ℝ) (v := 1) one_ne_zero h
      simp [Real.volume_Ioc] at this
      linarith
    exact ENNReal.lt_add_right (measure_ne_top _ _) hpos
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (cdf_nonneg _ _)).mp h1

lemma aux_adm_Phi_zero : stdNormalCdf 0 = 1 / 2 := by
  have := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (v := 1) one_ne_zero
  have hsymm : gaussianReal 0 1 (Set.Iic 0) = gaussianReal 0 1 (Set.Ioi 0) := by
    have h := gaussianReal_map_neg (μ := (0:ℝ)) (v := 1)
    simp only [neg_zero] at h
    conv_lhs => rw [← h]
    rw [Measure.map_apply measurable_neg measurableSet_Iic, measure_congr Ioi_ae_eq_Ici]
    congr 1
    ext x
    simp
  have hsum : gaussianReal 0 1 (Set.Iic 0) + gaussianReal 0 1 (Set.Ioi 0) = 1 := by
    rw [← measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Set.Iic_union_Ioi,
      measure_univ]
  rw [← hsymm] at hsum
  have h2 := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  unfold stdNormalCdf
  rw [cdf_eq_real, measureReal_def]
  simp at h2
  linarith

lemma aux_adm_avail_eq (P : Params) (hσ : 0 < P.sigmaL) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    availability P ρ = stdNormalCdf (P.lamL + 2 * P.zL * Real.sqrt (1 - ρ ^ 2)) := by
  have hr : 0 < 1 - ρ ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hr.le
  set s := lowSd P ρ with hs_def
  have hs : 0 < s := by
    simp only [hs_def, lowSd]
    exact mul_pos hσ (Real.sqrt_pos.2 hr)
  set V : NNReal := Real.toNNReal (s ^ 2) with hV
  set β : ℝ := ρ * P.sigmaL with hβ
  set c0 : ℝ := P.muL + 2 * P.zL * s with hc0
  have hmeasS : MeasurableSet ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iio c0) :=
    measurable_add measurableSet_Iio
  have hpt : ∀ x, lowDemandLaw P ρ x {y | y / 2 < orderQty P ρ x}
      = gaussianReal 0 V (Prod.mk ((-β) * x) ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iio c0)) := by
    intro x
    have hmap : lowDemandLaw P ρ x = (gaussianReal 0 V).map (· + lowMean P ρ x) := by
      rw [gaussianReal_map_add_const, zero_add]
      rfl
    rw [hmap, Measure.map_apply (measurable_add_const _)
      (measurableSet_lt (by fun_prop) measurable_const)]
    congr 1
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iio, orderQty, lowMean, hβ, hc0,
      ← hs_def]
    constructor <;> intro h <;> linarith
  have hconv : ((gaussianReal 0 1).map (fun x => (-β) * x)) ∗ gaussianReal 0 V
      = gaussianReal 0 (Real.toNNReal (P.sigmaL ^ 2)) := by
    rw [gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, hV,
        Real.coe_toNNReal _ (sq_nonneg _), hs_def, lowSd, hβ]
      rw [mul_pow, hsq]
      ring
  have hkey : ∫⁻ x, gaussianReal 0 V (Prod.mk ((-β) * x) ⁻¹'
        ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iio c0)) ∂(gaussianReal 0 1)
      = gaussianReal 0 (Real.toNNReal (P.sigmaL ^ 2)) (Set.Iio c0) := by
    rw [← hconv, Measure.conv, Measure.map_apply measurable_add measurableSet_Iio,
      Measure.prod_apply hmeasS,
      lintegral_map (measurable_measure_prodMk_left hmeasS) (by fun_prop)]
  have hfinal : gaussianReal 0 (Real.toNNReal (P.sigmaL ^ 2)) (Set.Iio c0)
      = gaussianReal 0 1 (Set.Iic (P.lamL + 2 * P.zL * Real.sqrt (1 - ρ ^ 2))) := by
    have := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (v := 1) one_ne_zero
    have hm : (gaussianReal 0 1).map (fun x => P.sigmaL * x)
        = gaussianReal 0 (Real.toNNReal (P.sigmaL ^ 2)) := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext
        simp [Real.coe_toNNReal _ (sq_nonneg _)]
    rw [← hm, Measure.map_apply (measurable_const_mul _) measurableSet_Iio,
      ← measure_congr Iio_ae_eq_Iic]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio]
    have hc : c0 / P.sigmaL = P.lamL + 2 * P.zL * Real.sqrt (1 - ρ ^ 2) := by
      simp only [hc0, hs_def, lowSd, Params.lamL]
      field_simp
    rw [← hc, lt_div_iff₀ hσ, mul_comm]
  unfold availability
  simp_rw [measureReal_def, hpt]
  rw [integral_toReal, hkey, hfinal, stdNormalCdf, cdf_eq_real, measureReal_def]
  · exact ((measurable_measure_prodMk_left hmeasS).comp (measurable_const_mul _)).aemeasurable
  · exact ae_of_all _ (fun x => measure_lt_top _ _)

end PreorderADI.Correlation

open PreorderADI.Correlation
open MeasureTheory ProbabilityTheory

theorem solution (P : Params) (hP : P.Standing)
    (h2c : 2 * P.c ≤ P.vL) :
    0 ≤ P.zL ∧ AntitoneOn (availability P) (Set.Ico (0:ℝ) 1) ∧
      (2 * P.c < P.vL → StrictAntiOn (availability P) (Set.Ico (0:ℝ) 1)) := by
  have hvL : 0 < P.vL := lt_trans hP.c_pos hP.c_lt_vL
  have hΦ := hP.zL_spec
  have hz : 0 ≤ P.zL := by
    by_contra h
    push Not at h
    have h1 := aux_adm_Phi_strictMono h
    rw [aux_adm_Phi_zero, hΦ, div_lt_iff₀ hvL] at h1
    linarith
  refine ⟨hz, ?_, ?_⟩
  · intro a ha b hb hab
    rw [aux_adm_avail_eq P hP.sigmaL_pos ha.1 ha.2, aux_adm_avail_eq P hP.sigmaL_pos hb.1 hb.2]
    apply aux_adm_Phi_strictMono.monotone
    have : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - a ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [ha.1])
    have := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 2 * P.zL)
    linarith
  · intro hlt a ha b hb hab
    have hzpos : 0 < P.zL := by
      by_contra h
      push Not at h
      have h1 := aux_adm_Phi_strictMono.monotone h
      rw [aux_adm_Phi_zero, hΦ, div_le_iff₀ hvL] at h1
      linarith
    rw [aux_adm_avail_eq P hP.sigmaL_pos ha.1 ha.2, aux_adm_avail_eq P hP.sigmaL_pos hb.1 hb.2]
    apply aux_adm_Phi_strictMono
    have : Real.sqrt (1 - b ^ 2) < Real.sqrt (1 - a ^ 2) :=
      Real.sqrt_lt_sqrt (by nlinarith [hb.2, hb.1]) (by nlinarith [ha.1])
    have := mul_lt_mul_of_pos_left this (by linarith : (0:ℝ) < 2 * P.zL)
    linarith
