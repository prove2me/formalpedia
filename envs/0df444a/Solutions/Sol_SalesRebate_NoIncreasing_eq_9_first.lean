-- Prove2me | solution 1 for SalesRebate.NoIncreasing.eq_9_first
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:11:50.60934+00:00
-- url     : https://prove2.me/submissions/24c8bc4c-2894-4d62-aeec-cbc131789583

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

open MeasureTheory ProbabilityTheory BlackScholesModel SalesRebate.NoIncreasing

namespace SRAux

lemma cdf_eq_integral (t : ℝ) :
    stdNormalCDF t = ∫ z in Set.Iic t, gaussianPDFReal 0 1 z := by
  unfold stdNormalCDF
  rw [← integral_const_mul]
  congr 1; ext z
  simp [gaussianPDFReal]

lemma cdf_eq_measureReal (t : ℝ) :
    stdNormalCDF t = (gaussianReal 0 1).real (Set.Iic t) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal,
    cdf_eq_integral]
  exact setIntegral_nonneg measurableSet_Iic (fun _ _ => gaussianPDFReal_nonneg _ _ _)

lemma cdf_eq_gaussian_Ici (m s t : ℝ) (hs : 0 < s) :
    stdNormalCDF ((m - t) / s) = (gaussianReal m (s ^ 2).toNNReal).real (Set.Ici t) := by
  have hmap : gaussianReal m (s ^ 2).toNNReal =
      (gaussianReal 0 1).map (fun z => (-s) * z + m) := by
    have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (-s)
    have h3 : (fun z : ℝ => (-s) * z + m) = (fun x => x + m) ∘ (fun x => (-s) * x) := rfl
    rw [h3, ← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_add_const]
    congr 1
    · ring
    · ext; simp [Real.toNNReal_of_nonneg (sq_nonneg s)]
  rw [hmap, cdf_eq_measureReal, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Ici]
  congr 2
  ext z
  simp only [Set.mem_Iic, Set.mem_preimage, Set.mem_Ici]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith


variable (M : Model) (hM : M.Valid)
include hM

lemma sigma_sq : M.σ ^ 2 = M.σε ^ 2 + M.σθ ^ 2 := by
  unfold Model.σ
  have := hM.σε_pos; have := hM.σθ_pos
  rw [Real.sq_sqrt (by positivity)]

lemma sigma_pos : 0 < M.σ := by
  unfold Model.σ
  have := hM.σε_pos
  exact Real.sqrt_pos.2 (by positivity)

lemma salesVolume_eq (c v : ℝ) :
    M.salesVolume c v = (gaussianReal v (M.σε ^ 2).toNNReal).real (Set.Ici c) :=
  cdf_eq_gaussian_Ici v M.σε c hM.σε_pos

lemma psi_eq (x : ℝ) : M.psi x = gaussianPDFReal M.θ (M.σ ^ 2).toNNReal x := by
  have hσ := sigma_pos M hM
  unfold Model.psi stdNormalPDF gaussianPDFReal
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  have h2 : Real.sqrt (2 * Real.pi * M.σ ^ 2) = Real.sqrt (2 * Real.pi) * M.σ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le]
  rw [h2]
  have h3 : -((M.θ - x) / M.σ) ^ 2 / 2 = -(x - M.θ) ^ 2 / (2 * M.σ ^ 2) := by
    field_simp; ring
  rw [h3]
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

lemma bayes (x v : ℝ) :
    gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v * gaussianPDFReal v (M.σε ^ 2).toNNReal x =
      gaussianPDFReal M.θ (M.σ ^ 2).toNNReal x *
        gaussianPDFReal (M.postMean x) M.σv2.toNNReal v := by
  have ha := hM.σθ_pos; have hb := hM.σε_pos
  have hv2 : 0 ≤ M.σv2 := by unfold Model.σv2; positivity
  unfold gaussianPDFReal
  rw [Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ (sq_nonneg _),
    Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ hv2, sigma_sq M hM]
  unfold Model.σv2 Model.postMean Model.tau
  set a := M.σθ ^ 2 with ha'
  set b := M.σε ^ 2 with hb'
  have hapos : 0 < a := by positivity
  have hbpos : 0 < b := by positivity
  have hpre : Real.sqrt (2 * Real.pi * a) * Real.sqrt (2 * Real.pi * b) =
      Real.sqrt (2 * Real.pi * (b + a)) * Real.sqrt (2 * Real.pi * (b * a / (b + a))) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexp : -(v - M.θ) ^ 2 / (2 * a) + -(x - v) ^ 2 / (2 * b) =
      -(x - M.θ) ^ 2 / (2 * (b + a)) +
        -(v - (a / (b + a) * x + (1 - a / (b + a)) * M.θ)) ^ 2 / (2 * (b * a / (b + a))) := by
    field_simp
    ring
  calc (Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (-(v - M.θ) ^ 2 / (2 * a)) *
        ((Real.sqrt (2 * Real.pi * b))⁻¹ * Real.exp (-(x - v) ^ 2 / (2 * b)))
      = (Real.sqrt (2 * Real.pi * a) * Real.sqrt (2 * Real.pi * b))⁻¹ *
          Real.exp (-(v - M.θ) ^ 2 / (2 * a) + -(x - v) ^ 2 / (2 * b)) := by
        rw [Real.exp_add, mul_inv]; ring
    _ = _ := by
        rw [hpre, hexp, Real.exp_add, mul_inv]; ring

lemma s1_ne : (M.σθ ^ 2).toNNReal ≠ 0 := by
  have := hM.σθ_pos; exact (Real.toNNReal_pos.2 (by positivity)).ne'

lemma s2_ne : (M.σε ^ 2).toNNReal ≠ 0 := by
  have := hM.σε_pos; exact (Real.toNNReal_pos.2 (by positivity)).ne'

lemma sT_ne : (M.σ ^ 2).toNNReal ≠ 0 := by
  have := sigma_pos M hM; exact (Real.toNNReal_pos.2 (by positivity)).ne'

lemma sv_ne : M.σv2.toNNReal ≠ 0 := by
  have := hM.σε_pos; have := hM.σθ_pos
  refine (Real.toNNReal_pos.2 ?_).ne'
  unfold Model.σv2; positivity

lemma key (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ v, |f v| ≤ C) (c : ℝ) :
    ∫ v, f v * M.salesVolume c v ∂M.prior =
      ∫ x in Set.Ioi c, (∫ v, f v ∂M.posterior x) * M.psi x := by
  set s1 := (M.σθ ^ 2).toNNReal
  set s2 := (M.σε ^ 2).toNNReal
  let F : ℝ → ℝ → ℝ := fun v x => gaussianPDFReal M.θ s1 v * f v *
    gaussianPDFReal v s2 x * (Set.Ici c).indicator 1 x
  have hL : ∫ v, f v * M.salesVolume c v ∂M.prior = ∫ v, ∫ x, F v x := by
    unfold Model.prior
    rw [integral_gaussianReal_eq_integral_smul (s1_ne M hM)]
    congr 1; ext v
    simp only [smul_eq_mul]
    rw [salesVolume_eq M hM, measureReal_def, gaussianReal_apply_eq_integral _ (s2_ne M hM),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ici
        (fun _ _ => gaussianPDFReal_nonneg _ _ _)),
      ← integral_indicator measurableSet_Ici, ← integral_const_mul, ← integral_const_mul]
    congr 1; ext x
    by_cases hx : x ∈ Set.Ici c
    · simp [F, hx]; ring
    · simp [F, hx]
  have hR : ∫ x in Set.Ioi c, (∫ v, f v ∂M.posterior x) * M.psi x = ∫ x, ∫ v, F v x := by
    rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
    congr 1; ext x
    by_cases hx : x ∈ Set.Ici c
    · simp only [Set.indicator_of_mem hx, F, Pi.one_apply, mul_one]
      unfold Model.posterior
      rw [integral_gaussianReal_eq_integral_smul (sv_ne M hM), psi_eq M hM,
        ← integral_mul_const]
      congr 1; ext v
      simp only [smul_eq_mul]
      have := bayes M hM x v
      linear_combination (f v) * this.symm
    · simp [F, hx]
  rw [hL, hR]
  -- integrability on the product
  let H : ℝ × ℝ → ℝ := fun z => gaussianPDFReal M.θ s1 z.1 * gaussianPDFReal z.1 s2 z.2
  have hg2 : Measurable (fun z : ℝ × ℝ => gaussianPDFReal z.1 s2 z.2) :=
    measurable_uncurry_gaussianPDFReal.comp
      (f := fun z : ℝ × ℝ => (z.1, s2, z.2)) (by fun_prop)
  have hg1 : Measurable (fun z : ℝ × ℝ => gaussianPDFReal M.θ s1 z.1) :=
    (measurable_gaussianPDFReal _ _).comp measurable_fst
  have hHmeas : Measurable H := hg1.mul hg2
  have hHint : Integrable H (volume.prod volume) := by
    refine (integrable_prod_iff hHmeas.aestronglyMeasurable).2 ⟨ae_of_all _ (fun v =>
      (integrable_gaussianPDFReal v s2).const_mul (gaussianPDFReal M.θ s1 v)), ?_⟩
    have : (fun v => ∫ x, ‖H (v, x)‖) = gaussianPDFReal M.θ s1 := by
      ext v
      simp only [H, Real.norm_eq_abs]
      simp_rw [abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
        (gaussianPDFReal_nonneg _ _ _))]
      rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ (s2_ne M hM), mul_one]
    rw [this]; exact integrable_gaussianPDFReal _ _
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine Integrable.mono' (hHint.const_mul C) ?_ (ae_of_all _ ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact ((hg1.mul (hf.comp measurable_fst)).mul hg2).mul
        ((measurable_one.indicator measurableSet_Ici).comp measurable_snd)
    · rintro ⟨v, x⟩
      simp only [Function.uncurry_apply_pair, F, H]
      have h1 := gaussianPDFReal_nonneg M.θ s1 v
      have h2 := gaussianPDFReal_nonneg v s2 x
      have hi0 : 0 ≤ (Set.Ici c).indicator (1 : ℝ → ℝ) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have hi1 : (Set.Ici c).indicator (1 : ℝ → ℝ) x ≤ 1 :=
        Set.indicator_le_self' (fun _ _ => zero_le_one) x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2,
        abs_of_nonneg hi0]
      calc gaussianPDFReal M.θ s1 v * |f v| * gaussianPDFReal v s2 x *
            (Set.Ici c).indicator 1 x
          ≤ gaussianPDFReal M.θ s1 v * |f v| * gaussianPDFReal v s2 x * 1 :=
            mul_le_mul_of_nonneg_left hi1 (by positivity)
        _ = |f v| * (gaussianPDFReal M.θ s1 v * gaussianPDFReal v s2 x) := by ring
        _ ≤ C * (gaussianPDFReal M.θ s1 v * gaussianPDFReal v s2 x) :=
            mul_le_mul_of_nonneg_right (hC v) (by positivity)
  exact integral_integral_swap hFint

lemma psi_setIntegral (c : ℝ) :
    ∫ x in Set.Ioi c, M.psi x = stdNormalCDF ((M.θ - c) / M.σ) := by
  rw [cdf_eq_gaussian_Ici M.θ M.σ c (sigma_pos M hM), measureReal_def,
    gaussianReal_apply_eq_integral _ (sT_ne M hM), ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Ici (fun _ _ => gaussianPDFReal_nonneg _ _ _)),
    integral_Ici_eq_integral_Ioi]
  exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => psi_eq M hM x)

omit hM in
lemma integrable_bdd {μ : Measure ℝ} [IsProbabilityMeasure μ] (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ v, |f v| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun v => by
    rw [Real.norm_eq_abs]; exact hC v))

theorem sales_volume_mean' (x : ℝ) :
    ∫ v, M.salesVolume x v ∂M.prior = stdNormalCDF ((M.θ - x) / M.σ) := by
  have := key M hM (fun _ => 1) measurable_const 1 (fun _ => by simp) x
  simp only [one_mul] at this
  rw [this, ← psi_setIntegral M hM]
  congr 1; ext y
  unfold Model.posterior
  simp

theorem eq_9_first' (p : ℝ) (rhat : ℝ → ℝ)
    (hmeas : Measurable rhat) (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (c : ℝ) :
    M.expectedProfit p rhat c = ∫ x in Set.Ioi c, (p - M.condReward rhat x) * M.psi x := by
  have hp : 0 ≤ p := (hbound 0).1.trans (hbound 0).2
  unfold Model.expectedProfit
  rw [key M hM (fun v => p - rhat v) (measurable_const.sub hmeas) p (fun v => by
    rw [abs_le]; constructor <;> linarith [(hbound v).1, (hbound v).2]) c]
  congr 1; ext x
  congr 1
  unfold Model.condReward Model.posterior
  rw [integral_sub (integrable_const p) (integrable_bdd rhat hmeas p (fun v => by
      rw [abs_of_nonneg (hbound v).1]; exact (hbound v).2))]
  simp

end SRAux

open SRAux

theorem solution (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hmeas : Measurable rhat) (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (c : ℝ) :
    M.expectedProfit p rhat c = ∫ x in Set.Ioi c, (p - M.condReward rhat x) * M.psi x :=
  eq_9_first' M hM p rhat hmeas hbound c
