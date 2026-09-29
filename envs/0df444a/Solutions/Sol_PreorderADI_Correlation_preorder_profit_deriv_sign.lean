-- Prove2me | solution 1 for PreorderADI.Correlation.preorder_profit_deriv_sign
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:15:01.069965+00:00
-- url     : https://prove2.me/submissions/561e035c-6ca2-487d-b215-8e52d484a8ff

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

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
    intro x; ext y; simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iio]
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
      ext y; simp only [Set.mem_setOf_eq, Set.mem_Iio]
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

theorem solution (P : Params) (hP : P.Standing)
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
