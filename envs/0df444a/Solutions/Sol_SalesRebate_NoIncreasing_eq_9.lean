-- Prove2me | solution 1 for SalesRebate.NoIncreasing.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:14:07.689615+00:00
-- url     : https://prove2.me/submissions/98221ec5-428c-42ee-9134-68f9a67db958

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Theorems.Thm_SalesRebate_NoIncreasing_eq_9_first
import Theorems.Thm_SalesRebate_NoIncreasing_sales_volume_mean

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

lemma psi_integrable : Integrable M.psi := by
  have : M.psi = gaussianPDFReal M.θ (M.σ ^ 2).toNNReal := funext (psi_eq M hM)
  rw [this]; exact integrable_gaussianPDFReal _ _

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

lemma condReward_mem (p : ℝ) (rhat : ℝ → ℝ) (hmeas : Measurable rhat)
    (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (x : ℝ) : M.condReward rhat x ∈ Set.Icc 0 p := by
  have hp : 0 ≤ p := (hbound 0).1.trans (hbound 0).2
  unfold Model.condReward Model.posterior
  have hint : Integrable rhat (gaussianReal (M.postMean x) M.σv2.toNNReal) := by
    exact integrable_bdd rhat hmeas p (fun v => by
      rw [abs_of_nonneg (hbound v).1]; exact (hbound v).2)
  constructor
  · exact integral_nonneg (fun v => (hbound v).1)
  · have := integral_mono hint (integrable_const p) (fun v => (hbound v).2)
    simpa using this

lemma condReward_measurable (rhat : ℝ → ℝ) (hmeas : Measurable rhat) :
    Measurable (M.condReward rhat) := by
  have heq : M.condReward rhat = fun x => ∫ v, gaussianPDFReal (M.postMean x) M.σv2.toNNReal v *
      rhat v := by
    ext x
    unfold Model.condReward Model.posterior
    rw [integral_gaussianReal_eq_integral_smul (sv_ne M hM)]
    rfl
  rw [heq]
  have hpm : Measurable M.postMean := by unfold Model.postMean; fun_prop
  have hj : Measurable (fun z : ℝ × ℝ => gaussianPDFReal (M.postMean z.1) M.σv2.toNNReal z.2 *
      rhat z.2) :=
    (measurable_uncurry_gaussianPDFReal.comp
      (f := fun z : ℝ × ℝ => (M.postMean z.1, M.σv2.toNNReal, z.2))
      (by fun_prop)).mul (hmeas.comp measurable_snd)
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma integrableOn_bdd_psi (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C)
    (s : Set ℝ) : IntegrableOn (fun x => g x * M.psi x) s := by
  refine Integrable.bdd_mul (psi_integrable M hM).integrableOn
    hg.aestronglyMeasurable (c := C) (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hC x))

end SRAux

open SRAux

open SalesRebate.NoIncreasing in
theorem solution (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hmeas : Measurable rhat) (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (c : ℝ)
    (hind : c - p + M.condReward rhat c = 0) :
    M.expectedProfit p rhat c = M.expectedProfit c (fun _ => 0) c +
      ∫ x in Set.Ioi c, (M.condReward rhat c - M.condReward rhat x) * M.psi x := by
  have hp : 0 ≤ p := (hbound 0).1.trans (hbound 0).2
  have hCRm := condReward_measurable M hM rhat hmeas
  have hCR := condReward_mem M hM p rhat hmeas hbound
  have h0 : M.expectedProfit c (fun _ => 0) c = ∫ x in Set.Ioi c, c * M.psi x := by
    unfold Model.expectedProfit
    simp only [sub_zero]
    rw [integral_const_mul, sales_volume_mean M hM, integral_const_mul, psi_setIntegral M hM]
  rw [eq_9_first M hM p rhat hmeas hbound c, h0, ← integral_add]
  · congr 1; ext x
    have : p = c + M.condReward rhat c := by linarith
    rw [this]; ring
  · exact (psi_integrable M hM).integrableOn.const_mul c
  · refine integrableOn_bdd_psi M hM _ (measurable_const.sub hCRm) p ?_ _
    intro x
    simp only [Pi.sub_apply]
    rw [abs_le]; constructor <;> linarith [(hCR x).1, (hCR x).2, (hCR c).1, (hCR c).2]

