-- Prove2me | solution 1 for PreorderADI.Correlation.preorder_profit_monotone_in_rho
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T00:53:25.687354+00:00
-- url     : https://prove2.me/submissions/e40fc633-e5fb-457f-9003-abd558cac1ee

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

set_option autoImplicit false

/- Complete checked body: AttributedCorrelation -/
section

/- Complete attributed body: Sol_PreorderADI_Correlation_preorder_profit_deriv_sign -/
section
-- Prove2me | solution 1 for PreorderADI.Correlation.preorder_profit_deriv_sign
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:15:01.069965+00:00
-- url     : https://prove2.me/submissions/561e035c-6ca2-487d-b215-8e52d484a8ff


open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

open scoped NNReal

lemma aux_ppds_shift (m t : ℝ) (V : ℝ≥0) :
    (gaussianReal m V).real (Set.Iio t) = (gaussianReal 0 V).real (Set.Iio (t - m)) := by
  have h : gaussianReal m V = (gaussianReal 0 V).map (· + m) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [h, map_measureReal_apply (by fun_prop) measurableSet_Iio]
  congr 1
  ext y
  simp [lt_sub_iff_add_lt]

lemma aux_ppds_joint (V : ℝ≥0) (β c0 : ℝ) :
    ∫ x, (gaussianReal 0 V).real (Set.Iio (c0 + β * x)) ∂(gaussianReal 0 1)
      = (gaussianReal 0 (NNReal.mk ((-β) ^ 2) (sq_nonneg _) * 1 + V)).real (Set.Iio c0) := by
  let S : Set (ℝ × ℝ) := {p | (-β) * p.1 + p.2 < c0}
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  have h1 : ∀ x : ℝ, Prod.mk x ⁻¹' S = Set.Iio (c0 + β * x) := by
    intro x; ext y; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  have hconv : ((gaussianReal 0 1).prod (gaussianReal 0 V)).map
      (fun p : ℝ × ℝ => (-β) * p.1 + p.2)
      = gaussianReal 0 (NNReal.mk ((-β) ^ 2) (sq_nonneg _) * 1 + V) := by
    have e : (fun p : ℝ × ℝ => (-β) * p.1 + p.2)
        = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x : ℝ => (-β) * x) id := by
      ext p; simp
    rw [e, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id,
      gaussianReal_map_const_mul]
    have := gaussianReal_conv_gaussianReal (m₁ := (-β) * 0) (m₂ := 0)
      (v₁ := NNReal.mk ((-β) ^ 2) (sq_nonneg _) * 1) (v₂ := V)
    unfold Measure.conv at this
    rw [this]
    simp
  have h2 : ((gaussianReal 0 1).prod (gaussianReal 0 V)).real S
      = ∫ x, (gaussianReal 0 V).real (Prod.mk x ⁻¹' S) ∂(gaussianReal 0 1) := by
    rw [measureReal_def, Measure.prod_apply hS, ← integral_toReal]
    · rfl
    · exact (measurable_measure_prodMk_left hS).aemeasurable
    · exact ae_of_all _ (fun x => measure_lt_top _ _)
  calc ∫ x, (gaussianReal 0 V).real (Set.Iio (c0 + β * x)) ∂(gaussianReal 0 1)
      = ∫ x, (gaussianReal 0 V).real (Prod.mk x ⁻¹' S) ∂(gaussianReal 0 1) := by
        simp_rw [h1]
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 V)).real S := h2.symm
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 V)).map
          (fun p : ℝ × ℝ => (-β) * p.1 + p.2)).real (Set.Iio c0) := by
        rw [map_measureReal_apply (by fun_prop) measurableSet_Iio]; rfl
    _ = _ := by rw [hconv]

lemma aux_ppds_cdf (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (c : ℝ) :
    (gaussianReal 0 v).real (Set.Iio c) = stdNormalCdf (c / σ) := by
  have hv' : v = NNReal.mk (σ ^ 2) (sq_nonneg _) * 1 := by ext; simp [hv]
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => σ * x) := by
    rw [gaussianReal_map_const_mul, hv', mul_zero]
  rw [hmap, map_measureReal_apply (by fun_prop) measurableSet_Iio]
  have hpre : (fun x => σ * x) ⁻¹' Set.Iio c = Set.Iio (c / σ) := by
    ext x; simp [lt_div_iff₀ hσ, mul_comm]
  rw [hpre, stdNormalCdf, cdf_eq_real]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact measureReal_congr Iio_ae_eq_Iic

lemma aux_ppds_avail (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) :
    availability P ρ = stdNormalCdf (2 * P.zL * Real.sqrt (1 - ρ ^ 2) + P.lamL) := by
  have h1 : ∀ x, (lowDemandLaw P ρ x).real {y | y / 2 < orderQty P ρ x}
      = (gaussianReal 0 (Real.toNNReal (lowSd P ρ ^ 2))).real
          (Set.Iio ((P.muL + 2 * P.zL * lowSd P ρ) + (ρ * P.sigmaL) * x)) := by
    intro x
    have hset : {y : ℝ | y / 2 < orderQty P ρ x} = Set.Iio (2 * orderQty P ρ x) := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_Iio]
      constructor <;> intro h <;> linarith
    rw [hset, lowDemandLaw, aux_ppds_shift]
    congr 2
    simp only [orderQty, lowMean]; ring
  unfold availability
  simp_rw [h1]
  rw [aux_ppds_joint, aux_ppds_cdf P.sigmaL hP.sigmaL_pos]
  · congr 1
    have := hP.sigmaL_pos
    rw [Params.lamL, lowSd]
    field_simp
    ring
  · have h0 : 0 ≤ 1 - ρ ^ 2 := by linarith
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one,
      Real.coe_toNNReal _ (sq_nonneg _)]
    simp only [lowSd, mul_pow, Real.sq_sqrt h0]
    ring

lemma aux_ppds_cdf_deriv (x : ℝ) : HasDerivAt stdNormalCdf (stdNormalPdf x) x := by
  have hcont : Continuous (gaussianPDFReal 0 1) := by
    unfold gaussianPDFReal; fun_prop
  have hint : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have hΦ : ∀ a, stdNormalCdf a = ∫ t in Set.Iic a, gaussianPDFReal 0 1 t := by
    intro a
    rw [stdNormalCdf, cdf_eq_real, measureReal_def,
      gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Iic (fun t _ => gaussianPDFReal_nonneg _ _ _)
  have heq : stdNormalCdf = fun u => stdNormalCdf 0 + ∫ t in (0:ℝ)..u, gaussianPDFReal 0 1 t := by
    funext u
    rw [hΦ, hΦ, ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
    ring
  rw [heq]
  exact ((hcont.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

lemma aux_ppds_cdf_zero : stdNormalCdf 0 = 1 / 2 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have h1 : (gaussianReal 0 1).real (Set.Iic 0) = (gaussianReal 0 1).real (Set.Ici 0) := by
    have := gaussianReal_map_neg (μ := 0) (v := 1)
    rw [neg_zero] at this
    conv_lhs => rw [← this]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1; ext x; simp
  have h2 : (gaussianReal 0 1).real (Set.Iic 0) + (gaussianReal 0 1).real (Set.Ioi 0) = 1 := by
    rw [← measureReal_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Set.Iic_union_Ioi,
      probReal_univ]
  have h3 : (gaussianReal 0 1).real (Set.Ioi 0) = (gaussianReal 0 1).real (Set.Ici 0) :=
    measureReal_congr Ioi_ae_eq_Ici
  rw [stdNormalCdf, cdf_eq_real]
  linarith

lemma aux_ppds_zL_neg (P : Params) (hP : P.Standing) (h2c : P.vL < 2 * P.c) : P.zL < 0 := by
  by_contra h
  push Not at h
  have hvL : 0 < P.vL := lt_trans hP.c_pos hP.c_lt_vL
  have hmono : stdNormalCdf 0 ≤ stdNormalCdf P.zL := monotone_cdf _ h
  rw [aux_ppds_cdf_zero, hP.zL_spec] at hmono
  rw [le_div_iff₀ hvL] at hmono
  linarith

end PreorderADI.Correlation

open PreorderADI.Correlation

theorem checked_preorder_profit_deriv_sign (P : Params) (hP : P.Standing)
    (h2c : P.vL < 2 * P.c) (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (preorderProfit P) d ρ ∧
      (0 < d ↔ P.muH < threshold P ρ) ∧ (d < 0 ↔ threshold P ρ < P.muH) := by
  obtain ⟨hρ0, hρ1⟩ := hρ
  have hs2 : 0 < 1 - ρ ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.mpr hs2
  have hzL := aux_ppds_zL_neg P hP h2c
  have hΔ : 0 < P.Delta := by unfold Params.Delta; linarith [hP.vL_lt_delta_vH]
  have hvL : 0 < P.vL := lt_trans hP.c_pos hP.c_lt_vL
  set w := 2 * P.zL * Real.sqrt (1 - ρ ^ 2) + P.lamL with hw_def
  set K := 2 * P.Delta * P.zL * stdNormalPdf w with hK_def
  set A := P.vL * stdNormalPdf P.zL * P.sigmaL with hA_def
  have hφw : 0 < stdNormalPdf w := gaussianPDFReal_pos 0 1 w one_ne_zero
  have hφz : 0 < stdNormalPdf P.zL := gaussianPDFReal_pos 0 1 P.zL one_ne_zero
  have hK : K < 0 := by
    have : 0 < 2 * P.Delta * stdNormalPdf w := by positivity
    have h' : K = (2 * P.Delta * stdNormalPdf w) * P.zL := by rw [hK_def]; ring
    rw [h']; exact mul_neg_of_pos_of_neg this hzL
  have hA : 0 < A := by have := hP.sigmaL_pos; positivity
  have hq : 0 < ρ / Real.sqrt (1 - ρ ^ 2) := div_pos hρ0 hs
  -- derivative of √(1 - r²)
  have hg : HasDerivAt (fun r : ℝ => Real.sqrt (1 - r ^ 2))
      (-(ρ / Real.sqrt (1 - ρ ^ 2))) ρ := by
    have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * ρ)) ρ := by
      simpa using (hasDerivAt_pow 2 ρ).const_sub 1
    have := h1.sqrt hs2.ne'
    convert this using 1
    field_simp
  -- closed form of the profit near ρ
  let F : ℝ → ℝ := fun r =>
    (P.vH - P.Delta * stdNormalCdf (2 * P.zL * Real.sqrt (1 - r ^ 2) + P.lamL) - P.c) * P.muH
      + ((P.vL - P.c) * P.muL - A * Real.sqrt (1 - r ^ 2))
  have hF : HasDerivAt F
      (-(P.Delta * (stdNormalPdf w * (2 * P.zL * -(ρ / Real.sqrt (1 - ρ ^ 2))))) * P.muH
        + -(A * -(ρ / Real.sqrt (1 - ρ ^ 2)))) ρ := by
    have hwd : HasDerivAt (fun r : ℝ => 2 * P.zL * Real.sqrt (1 - r ^ 2) + P.lamL)
        (2 * P.zL * -(ρ / Real.sqrt (1 - ρ ^ 2))) ρ :=
      (hg.const_mul (2 * P.zL)).add_const P.lamL
    have hΦ := (aux_ppds_cdf_deriv w).comp ρ hwd
    have h1 := (((hΦ.const_mul P.Delta).const_sub P.vH).sub_const P.c).mul_const P.muH
    have h2 := (hg.const_mul A).const_sub ((P.vL - P.c) * P.muL)
    have := h1.add h2
    exact this
  have hev : preorderProfit P =ᶠ[nhds ρ] F := by
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ nhds ρ := Ioo_mem_nhds (by linarith) hρ1
    filter_upwards [hmem] with r hr
    obtain ⟨hr0, hr1⟩ := hr
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    simp only [preorderProfit, F, aux_ppds_avail P hP r hr2, secondProfit, hA_def]
    ring
  refine ⟨(ρ / Real.sqrt (1 - ρ ^ 2)) * (K * P.muH + A), ?_, ?_, ?_⟩
  · refine (hF.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [hK_def]; ring
  · have ht : threshold P ρ = -A / K := by rw [threshold, hA_def, hK_def, hw_def]
    rw [ht, lt_div_iff_of_neg hK]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · have ht : threshold P ρ = -A / K := by rw [threshold, hA_def, hK_def, hw_def]
    rw [ht, div_lt_iff_of_neg hK]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
end

/- Complete attributed body: Sol_PreorderADI_Correlation_availability_decreasing_high_margin -/
section
-- Prove2me | solution 1 for PreorderADI.Correlation.availability_decreasing_high_margin
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:01:28.860403+00:00
-- url     : https://prove2.me/submissions/486361b0-4706-475c-b04a-1529952a60b7


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

theorem checked_availability_decreasing_high_margin (P : Params) (hP : P.Standing)
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
end


end

/- Complete checked body: ProfitRegularity -/
section

namespace PreorderADI.CorrelationProof
open PreorderADI.Correlation

noncomputable def profitFormula (P : Params) (ρ : ℝ) : ℝ :=
  (P.vH - P.Delta * stdNormalCdf (2 * P.zL * Real.sqrt (1 - ρ ^ 2) + P.lamL) - P.c) * P.muH
    + (P.vL - P.c) * P.muL - P.vL * stdNormalPdf P.zL * P.sigmaL * Real.sqrt (1 - ρ ^ 2)

theorem profit_eq_formula (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) :
    preorderProfit P ρ = profitFormula P ρ := by
  rw [preorderProfit, aux_ppds_avail P hP ρ hρ]
  unfold secondProfit profitFormula
  ring

theorem profitFormula_continuous (P : Params) : Continuous (profitFormula P) := by
  have hPhi : Continuous stdNormalCdf :=
    continuous_iff_continuousAt.mpr (fun x => (aux_ppds_cdf_deriv x).continuousAt)
  unfold profitFormula
  fun_prop

theorem profit_continuousOn (P : Params) (hP : P.Standing) :
    ContinuousOn (preorderProfit P) (Set.Ico (0 : ℝ) 1) := by
  apply (profitFormula_continuous P).continuousOn.congr
  intro ρ hρ
  exact profit_eq_formula P hP ρ (by nlinarith [hρ.1, hρ.2])

end PreorderADI.CorrelationProof

end

/- Complete checked body: ThresholdLevels -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace PreorderADI.CorrelationProof
open PreorderADI.Correlation

noncomputable def normalArgument (P : Params) (r : ℝ) : ℝ :=
  2 * P.zL * Real.sqrt (1-r^2) + P.lamL

theorem normalArgument_strictMono (P : Params) (hz : P.zL < 0) :
    StrictMonoOn (normalArgument P) (Set.Ico (0:ℝ) 1) := by
  intro a ha b hb hab
  have hs : Real.sqrt (1-b^2) < Real.sqrt (1-a^2) :=
    Real.sqrt_lt_sqrt (by nlinarith [hb.1,hb.2]) (by nlinarith [ha.1])
  have hm := mul_lt_mul_of_neg_left hs (show 2*P.zL < 0 by linarith)
  dsimp [normalArgument]
  linarith

theorem normalPdf_eq_implies_sq_eq {a b : ℝ} (h : stdNormalPdf a = stdNormalPdf b) :
    a^2=b^2 := by
  simp only [stdNormalPdf,gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero] at h
  have hc : (Real.sqrt (2*Real.pi))⁻¹ ≠ 0 := by positivity
  have he := mul_left_cancel₀ hc h
  have hh := Real.exp_injective he
  linarith

theorem threshold_eq_implies_argument_sq_eq (P : Params) (hP : P.Standing)
    (hz : P.zL < 0) {a b : ℝ} (h : threshold P a = threshold P b) :
    normalArgument P a ^ 2 = normalArgument P b ^ 2 := by
  let A := P.vL * stdNormalPdf P.zL * P.sigmaL
  let B := 2*P.Delta*P.zL
  have hΔ : 0 < P.Delta := sub_pos.mpr hP.vL_lt_delta_vH
  have hv : 0 < P.vL := lt_trans hP.c_pos hP.c_lt_vL
  have hφz : 0 < stdNormalPdf P.zL := gaussianPDFReal_pos 0 1 P.zL one_ne_zero
  have hA : 0 < A := mul_pos (mul_pos hv hφz) hP.sigmaL_pos
  have hB : B ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hΔ.ne') hz.ne
  have haφ : stdNormalPdf (normalArgument P a) ≠ 0 :=
    (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne'
  have hbφ : stdNormalPdf (normalArgument P b) ≠ 0 :=
    (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne'
  change -A / (B*stdNormalPdf (normalArgument P a)) =
    -A / (B*stdNormalPdf (normalArgument P b)) at h
  have hh := (div_eq_div_iff (mul_ne_zero hB haφ) (mul_ne_zero hB hbφ)).mp h
  have he : (-A*B)*stdNormalPdf (normalArgument P b) =
      (-A*B)*stdNormalPdf (normalArgument P a) := by
    calc
      _ = -A*(B*stdNormalPdf (normalArgument P b)) := by ring
      _ = -A*(B*stdNormalPdf (normalArgument P a)) := hh
      _ = _ := by ring
  have hp := mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hA.ne') hB) he
  exact normalPdf_eq_implies_sq_eq hp.symm

/-- A threshold level cannot contain three ordered correlations. -/
theorem threshold_no_three (P : Params) (hP : P.Standing) (hz : P.zL < 0)
    {a b c : ℝ} (ha : a ∈ Set.Ico (0:ℝ) 1) (hb : b ∈ Set.Ico (0:ℝ) 1)
    (hc : c ∈ Set.Ico (0:ℝ) 1) (hab : a<b) (hbc : b<c)
    (hab' : threshold P a = threshold P b) (hbc' : threshold P b = threshold P c) :
    False := by
  have h1 := normalArgument_strictMono P hz ha hb hab
  have h2 := normalArgument_strictMono P hz hb hc hbc
  have hs1 := threshold_eq_implies_argument_sq_eq P hP hz hab'
  have hs2 := threshold_eq_implies_argument_sq_eq P hP hz hbc'
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs1 with he | he
  · linarith
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs2 with hf | hf <;> linarith

end PreorderADI.CorrelationProof

end

/- Complete checked body: ConstantIntervals -/
section

set_option autoImplicit false
open Filter Topology

namespace PreorderADI.CorrelationProof

theorem deriv_eq_zero_of_constant_interval (f : ℝ → ℝ) {a b r : ℝ}
    (hr : r ∈ Set.Ioo a b) (h : ∀ t ∈ Set.Icc a b, f t = f a) :
    deriv f r = 0 := by
  have he : f =ᶠ[𝓝 r] (fun _ => f a) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    exact h t ⟨ht.1.le,ht.2.le⟩
  exact ((hasDerivAt_const r (f a)).congr_of_eventuallyEq he).deriv

theorem antitone_constant_interval {D : Set ℝ} (hD : D.OrdConnected) {f : ℝ → ℝ}
    (hf : AntitoneOn f D) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D)
    (he : f a = f b) : ∀ t ∈ Set.Icc a b, f t = f a := by
  intro t ht
  have htD := hD.out ha hb ht
  apply le_antisymm (hf ha htD ht.1)
  rw [he]
  exact hf htD hb ht.2

end PreorderADI.CorrelationProof

end

/- Complete checked body: LowMargin -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace PreorderADI.CorrelationProof
open PreorderADI.Correlation

theorem low_margin_profit_monotonicity (P : Params) (hP : P.Standing)
    (h2c : P.vL < 2*P.c) (I : Set ℝ) (hI : I ⊆ Set.Ico (0:ℝ) 1)
    (hconn : I.OrdConnected) :
    ((∀ r ∈ I,P.muH < threshold P r) → StrictMonoOn (preorderProfit P) I) ∧
    ((∀ r ∈ I,threshold P r ≤ P.muH) → StrictAntiOn (preorderProfit P) I) := by
  have hcont := (profit_continuousOn P hP).mono hI
  have hinterior {r : ℝ} (hr : r ∈ interior I) : r ∈ Set.Ioo (0:ℝ) 1 := by
    have hh := interior_mono hI hr
    simpa only [interior_Ico] using hh
  constructor
  · intro hT
    apply strictMonoOn_of_deriv_pos hconn.convex hcont
    intro r hr
    obtain ⟨d,hd,hpos,_⟩ := checked_preorder_profit_deriv_sign P hP h2c r (hinterior hr)
    rw [hd.deriv]
    exact hpos.mpr (hT r (interior_subset hr))
  · intro hT
    have hanti : AntitoneOn (preorderProfit P) I := by
      apply antitoneOn_of_deriv_nonpos hconn.convex hcont
      · intro r hr
        obtain ⟨d,hd,_,_⟩ := checked_preorder_profit_deriv_sign P hP h2c r (hinterior hr)
        exact hd.differentiableAt.differentiableWithinAt
      · intro r hr
        obtain ⟨d,hd,hpos,_⟩ := checked_preorder_profit_deriv_sign P hP h2c r (hinterior hr)
        rw [hd.deriv]
        exact le_of_not_gt (fun h => (not_lt_of_ge (hT r (interior_subset hr))) (hpos.mp h))
    intro a ha b hb hab
    by_contra hn
    have he : preorderProfit P a = preorderProfit P b :=
      le_antisymm (le_of_not_gt hn) (hanti ha hb hab.le)
    have hconstant := antitone_constant_interval hconn hanti ha hb he
    have hlevel (r : ℝ) (hr : r ∈ Set.Ioo a b) : threshold P r = P.muH := by
      have hrI := hconn.out ha hb ⟨hr.1.le,hr.2.le⟩
      have hr0 : r ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_lt (hI ha).1 hr.1,
        lt_trans hr.2 (hI hb).2⟩
      obtain ⟨d,hd,_,hneg⟩ := checked_preorder_profit_deriv_sign P hP h2c r hr0
      have hz := deriv_eq_zero_of_constant_interval (preorderProfit P) hr hconstant
      rw [hd.deriv] at hz
      apply le_antisymm (hT r hrI)
      exact le_of_not_gt (fun h => (by linarith : ¬ d < 0) (hneg.mpr h))
    let u := (3*a+b)/4
    let v := (a+b)/2
    let w := (a+3*b)/4
    have hu : u ∈ Set.Ioo a b := by dsimp [u]; constructor <;> linarith
    have hv : v ∈ Set.Ioo a b := by dsimp [v]; constructor <;> linarith
    have hw : w ∈ Set.Ioo a b := by dsimp [w]; constructor <;> linarith
    have huv : u<v := by dsimp [u,v]; linarith
    have hvw : v<w := by dsimp [v,w]; linarith
    have hsub : Set.Ioo a b ⊆ Set.Ico (0:ℝ) 1 := by
      intro r hr
      exact hI (hconn.out ha hb ⟨hr.1.le,hr.2.le⟩)
    exact threshold_no_three P hP (aux_ppds_zL_neg P hP h2c)
      (hsub hu) (hsub hv) (hsub hw) huv hvw
      ((hlevel u hu).trans (hlevel v hv).symm)
      ((hlevel v hv).trans (hlevel w hw).symm)

end PreorderADI.CorrelationProof

end

/- Complete checked body: HighMargin -/
section

namespace PreorderADI.CorrelationProof
open PreorderADI.Correlation ProbabilityTheory

theorem secondProfit_zero_strictMono (P : Params) (hP : P.Standing) :
    StrictMonoOn (fun ρ => secondProfit P ρ 0) (Set.Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hv : 0 < P.vL := hP.c_pos.trans hP.c_lt_vL
  have hd : 0 < stdNormalPdf P.zL := gaussianPDFReal_pos 0 1 P.zL one_ne_zero
  have hcoef : 0 < P.vL * stdNormalPdf P.zL * P.sigmaL :=
    mul_pos (mul_pos hv hd) hP.sigmaL_pos
  have hs : Real.sqrt (1 - b ^ 2) < Real.sqrt (1 - a ^ 2) :=
    Real.sqrt_lt_sqrt (by nlinarith [hb.1, hb.2]) (by nlinarith [ha.1])
  have hh := mul_lt_mul_of_pos_left hs hcoef
  simp only [secondProfit, mul_zero, add_zero]
  linarith

theorem high_margin_profit_strictMono (P : Params) (hP : P.Standing)
    (h2c : 2 * P.c ≤ P.vL) :
    StrictMonoOn (preorderProfit P) (Set.Ico (0 : ℝ) 1) := by
  have ha := (checked_availability_decreasing_high_margin P hP h2c).2.1
  intro a hia b hib hab
  have hA := ha hia hib hab.le
  have hS := secondProfit_zero_strictMono P hP hia hib hab
  have hD : 0 < P.Delta := sub_pos.mpr hP.vL_lt_delta_vH
  have hterm := mul_le_mul_of_nonneg_left hA (mul_pos hD hP.muH_pos).le
  unfold preorderProfit
  nlinarith

end PreorderADI.CorrelationProof

end

/- Complete checked body: PreorderRoot -/
section

namespace PreorderADI.Correlation

theorem preorder_profit_monotone_in_rho (P : Params) (hP : P.Standing) :
    (P.vL < 2 * P.c →
      ∀ I ⊆ Set.Ico (0:ℝ) 1, I.OrdConnected →
        ((∀ ρ ∈ I, P.muH < threshold P ρ) → StrictMonoOn (preorderProfit P) I) ∧
        ((∀ ρ ∈ I, threshold P ρ ≤ P.muH) → StrictAntiOn (preorderProfit P) I)) ∧
    (2 * P.c ≤ P.vL → StrictMonoOn (preorderProfit P) (Set.Ico (0:ℝ) 1)) := by
  exact ⟨fun h2c I hI hconn =>
    PreorderADI.CorrelationProof.low_margin_profit_monotonicity P hP h2c I hI hconn,
    fun h2c => PreorderADI.CorrelationProof.high_margin_profit_strictMono P hP h2c⟩

end PreorderADI.Correlation

end

open PreorderADI.Correlation
open MeasureTheory ProbabilityTheory

theorem solution (P : Params) (hP : P.Standing) :
    (P.vL < 2 * P.c →
      ∀ I ⊆ Set.Ico (0:ℝ) 1, I.OrdConnected →
        ((∀ ρ ∈ I, P.muH < threshold P ρ) → StrictMonoOn (preorderProfit P) I) ∧
        ((∀ ρ ∈ I, threshold P ρ ≤ P.muH) → StrictAntiOn (preorderProfit P) I)) ∧
    (2 * P.c ≤ P.vL → StrictMonoOn (preorderProfit P) (Set.Ico (0:ℝ) 1)) := by
  exact PreorderADI.Correlation.preorder_profit_monotone_in_rho P hP

#print axioms PreorderADI.Correlation.preorder_profit_monotone_in_rho
#print axioms solution
