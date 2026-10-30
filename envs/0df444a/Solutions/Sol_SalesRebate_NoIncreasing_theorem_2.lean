-- Prove2me | solution 1 for SalesRebate.NoIncreasing.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:17:16.830363+00:00
-- url     : https://prove2.me/submissions/6311a4c0-0b16-453b-bbf6-1335ed909756

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Theorems.Thm_SalesRebate_NoIncreasing_lemma_1
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

lemma psi_nonneg (x : ℝ) : 0 ≤ M.psi x := by
  rw [psi_eq M hM]; exact gaussianPDFReal_nonneg _ _ _

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

lemma psi_setIntegral_pos (c : ℝ) : 0 < ∫ x in Set.Ioi c, M.psi x := by
  have hT := sT_ne M hM
  have h1 : ∫ x in Set.Ioi c, M.psi x = (gaussianReal M.θ (M.σ ^ 2).toNNReal).real (Set.Ioi c) := by
    rw [measureReal_def, gaussianReal_apply_eq_integral _ hT, ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Ioi (fun _ _ => gaussianPDFReal_nonneg _ _ _))]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => psi_eq M hM x)
  rw [h1, measureReal_def]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  intro h0
  have := gaussianReal_absolutelyContinuous' M.θ hT h0
  simp at this

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

omit hM in
lemma cdf_mem (t : ℝ) : stdNormalCDF t ∈ Set.Icc 0 1 := by
  rw [cdf_eq_measureReal]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

omit hM in
lemma cdf_mono : Monotone stdNormalCDF := by
  intro a b hab
  rw [cdf_eq_measureReal, cdf_eq_measureReal]
  exact measureReal_mono (Set.Iic_subset_Iic.2 hab)

lemma postMean_mono : Monotone M.postMean := by
  intro x y hxy
  unfold Model.postMean
  have : 0 ≤ M.tau := by unfold Model.tau; positivity
  nlinarith

lemma condReward_mono (p : ℝ) (rhat : ℝ → ℝ) (hmono : Monotone rhat)
    (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) : Monotone (M.condReward rhat) := by
  have hmeas : Measurable rhat := hmono.measurable
  intro x y hxy
  unfold Model.condReward Model.posterior
  have hmap : ∀ m : ℝ, gaussianReal m M.σv2.toNNReal =
      (gaussianReal 0 M.σv2.toNNReal).map (· + m) := by
    intro m; rw [gaussianReal_map_add_const, zero_add]
  rw [hmap (M.postMean x), hmap (M.postMean y),
    integral_map (by fun_prop) hmeas.aestronglyMeasurable,
    integral_map (by fun_prop) hmeas.aestronglyMeasurable]
  have hb : ∀ m : ℝ, ∀ w, |rhat (w + m)| ≤ p := fun m w => by
    rw [abs_of_nonneg (hbound _).1]; exact (hbound _).2
  refine integral_mono (integrable_bdd _ (hmeas.comp (by fun_prop)) p (hb _))
    (integrable_bdd _ (hmeas.comp (by fun_prop)) p (hb _)) (fun w => ?_)
  exact hmono (add_le_add_right (postMean_mono M hM hxy) w)

end SRAux

open SRAux

open SalesRebate.NoIncreasing in
theorem solution (M : Model) (hM : M.Valid) (p : ℝ) (hp : M.IsMarketPrice p)
    (r : ℝ → ℝ) (hr : IsRewardProgram p r) (hmono : MonotoneOn r (Set.Icc 0 1))
    (c : ℝ) (hc : M.IsEquilibriumCutoff p (M.rhat r c) c) :
    ¬ M.IsProfitable p r c := by
  set rhat := M.rhat r c with hrhat
  have hSV : ∀ v, M.salesVolume c v ∈ Set.Icc 0 1 := fun v => cdf_mem _
  have hbound : ∀ v, rhat v ∈ Set.Icc 0 p := fun v => hr _ (hSV v)
  have hrmono : Monotone rhat := by
    intro a b hab
    refine hmono (hSV a) (hSV b) (cdf_mono ?_)
    exact div_le_div_of_nonneg_right (by linarith) hM.σε_pos.le
  have hmeas : Measurable rhat := hrmono.measurable
  have hCR := condReward_mem M hM p rhat hmeas hbound
  have hCRm := condReward_measurable M hM rhat hmeas
  have hCRmono := condReward_mono M hM p rhat hrmono hbound
  -- Step 1 (Lemmas 1 and 5): the program does no better than the plain price `c`.
  have h1 : M.expectedProfit p rhat c ≤ M.expectedProfit c (fun _ => 0) c := by
    by_contra hlt
    push_neg at hlt
    have h := (lemma_1 M hM p rhat hmeas hbound c hc).1 hlt
    rw [div_lt_iff₀ (psi_setIntegral_pos M hM c)] at h
    have hge : M.condReward rhat c * ∫ x in Set.Ioi c, M.psi x ≤
        ∫ x in Set.Ioi c, M.condReward rhat x * M.psi x := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on ((psi_integrable M hM).integrableOn.const_mul _)
        (integrableOn_bdd_psi M hM _ hCRm p (fun x => by
          rw [abs_of_nonneg (hCR x).1]; exact (hCR x).2) _) measurableSet_Ioi ?_
      intro x hx
      exact mul_le_mul_of_nonneg_right (hCRmono (le_of_lt hx)) (psi_nonneg M hM x)
    linarith
  -- Step 2 (Assumption 1): the plain price `c` does no better than the market price `p`.
  have h2 : M.expectedProfit c (fun _ => 0) c ≤ M.expectedProfit p (fun _ => 0) p := by
    unfold Model.expectedProfit
    simp only [sub_zero]
    rw [integral_const_mul, integral_const_mul, sales_volume_mean M hM, sales_volume_mean M hM]
    rcases le_or_gt 0 c with hc0 | hc0
    · exact hp c hc0
    · have := hp 0 le_rfl
      have := (cdf_mem ((M.θ - c) / M.σ)).1
      simp only [zero_mul] at *
      nlinarith
  unfold Model.IsProfitable
  linarith


