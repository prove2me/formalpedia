-- Prove2me | solution 1 for PhiSobBayes.eq_49
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:24:53.355844+00:00
-- url     : https://prove2.me/submissions/4d7daadc-1660-4499-a55d-7779086de476

import Mathlib
import Definitions.Def_PhiSobBayes_posterior
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_AdmissiblePhi
import Definitions.Def_PhiSobBayes_testClass
import Theorems.Thm_PhiSobBayes_eq_46_posterior_averaging
import Theorems.Thm_PhiSobBayes_lemma_6_1
import Theorems.Thm_PhiSobBayes_lemma_6_2
import Theorems.Thm_PhiSobBayes_fact_A_22


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace PSBC

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def lik (t : ℝ) (y x : E) : ℝ := Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2)

lemma lik_pos (t : ℝ) (y x : E) : 0 < lik t y x := Real.exp_pos _

lemma lik_le_one (t : ℝ) (y x : E) : lik t y x ≤ 1 := by
  unfold lik; rw [Real.exp_le_one_iff]
  have := sq_nonneg ‖y - Real.sqrt t • x‖; linarith

lemma continuous_lik (t : ℝ) : Continuous (fun p : E × E => lik t p.1 p.2) := by
  unfold lik; fun_prop

lemma integrable_lik (μ : Measure E) [IsFiniteMeasure μ] (t : ℝ) (y : E) :
    Integrable (fun x => lik t y x) μ := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact ((continuous_lik t).comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (lik_pos t y x)]; exact lik_le_one t y x

def Z (μ : Measure E) (t : ℝ) (y : E) : ℝ := ∫ x, lik t y x ∂μ

lemma Z_pos (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (y : E) : 0 < Z μ t y := by
  unfold Z
  rw [integral_pos_iff_support_of_nonneg (fun x => (lik_pos t y x).le) (integrable_lik μ t y)]
  have : Function.support (fun x => lik t y x) = Set.univ :=
    Set.eq_univ_of_forall fun x => (lik_pos t y x).ne'
  rw [this]; simp

lemma Z_le_one (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (y : E) : Z μ t y ≤ 1 := by
  unfold Z
  calc ∫ x, lik t y x ∂μ ≤ ∫ _x, (1:ℝ) ∂μ :=
        integral_mono (integrable_lik μ t y) (integrable_const _) (fun x => lik_le_one t y x)
    _ = 1 := by simp

lemma measurable_Z (μ : Measure E) [IsFiniteMeasure μ] (t : ℝ) : Measurable (Z μ t) := by
  unfold Z
  have : StronglyMeasurable (fun p : E × E => lik t p.1 p.2) :=
    (continuous_lik t).stronglyMeasurable
  exact (this.integral_prod_right' (ν := μ)).measurable

def dens (μ : Measure E) (t : ℝ) (y x : E) : ℝ≥0∞ := ENNReal.ofReal (lik t y x / Z μ t y)

lemma measurable_dens (μ : Measure E) [IsFiniteMeasure μ] (t : ℝ) :
    Measurable (Function.uncurry (dens μ t)) := by
  unfold dens
  refine ENNReal.measurable_ofReal.comp (Measurable.div ?_ ?_)
  · exact (continuous_lik t).measurable
  · exact (measurable_Z μ t).comp measurable_fst

lemma posterior_eq (μ : Measure E) (t : ℝ) (y : E) :
    PhiSobBayes.posterior μ t y = μ.withDensity (dens μ t y) := rfl

def postK (μ : Measure E) [IsFiniteMeasure μ] (t : ℝ) : Kernel E E :=
  Kernel.withDensity (Kernel.const E μ) (dens μ t)

lemma postK_apply (μ : Measure E) [IsFiniteMeasure μ] (t : ℝ) (y : E) :
    postK μ t y = PhiSobBayes.posterior μ t y := by
  unfold postK
  rw [Kernel.withDensity_apply _ (measurable_dens μ t), Kernel.const_apply]; rfl

lemma posterior_univ (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (y : E) :
    PhiSobBayes.posterior μ t y Set.univ = 1 := by
  rw [posterior_eq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold dens
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div]
    have h := (Z_pos μ t y).ne'
    change ENNReal.ofReal (Z μ t y / Z μ t y) = 1
    rw [div_self h]; simp
  · exact (integrable_lik μ t y).div_const _
  · exact Filter.Eventually.of_forall fun x => div_nonneg (lik_pos t y x).le (Z_pos μ t y).le

instance posterior_isProb (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (y : E) :
    IsProbabilityMeasure (PhiSobBayes.posterior μ t y) := ⟨posterior_univ μ t y⟩

instance postK_isMarkov (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    IsMarkovKernel (postK μ t) :=
  ⟨fun y => by rw [postK_apply]; infer_instance⟩

end PSBC



set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

noncomputable section

namespace PSBC

lemma adm_contOn {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : PhiSobBayes.AdmissiblePhi J Φ) :
    ContinuousOn Φ J := hΦ.1.continuousOn

lemma adm_contOn_d1 {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) : ContDiffOn ℝ ∞ (deriv Φ) J :=
  hΦ.1.deriv_of_isOpen hJ.1 (by simp)

lemma adm_contOn_d2 {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) : ContDiffOn ℝ ∞ (deriv (deriv Φ)) J :=
  (adm_contOn_d1 hJ hΦ).deriv_of_isOpen hJ.1 (by simp)

lemma adm_convex {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) : ConvexOn ℝ J Φ := by
  refine convexOn_of_deriv2_nonneg' hJ.2.1.convex ?_ ?_ ?_
  · exact hΦ.1.differentiableOn (by simp)
  · exact (adm_contOn_d1 hJ hΦ).differentiableOn (by simp)
  · intro x hx; simpa using (hΦ.2.1 x hx).le

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma tc_contDiff {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ContDiff ℝ ∞ f := by
  obtain ⟨⟨c, g, hg, -, rfl⟩, -⟩ := hf
  exact contDiff_const.add hg

lemma tc_cont {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) : Continuous f :=
  (tc_contDiff hf).continuous

/-- for a test function, `h ∘ f - h c` has compact support -/
lemma tc_comp_sub_hasCompactSupport {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ c : ℝ, ∀ h : ℝ → ℝ, HasCompactSupport (fun x => h (f x) - h c) := by
  obtain ⟨⟨c, g, hg, hgc, rfl⟩, -⟩ := hf
  refine ⟨c, fun h => ?_⟩
  refine hgc.mono ?_
  intro x hx
  by_contra h0
  apply hx
  have : g x = 0 := Function.notMem_support.mp h0
  simp [this]

lemma tc_bounded_comp {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) (h : ℝ → ℝ)
    (hh : ContinuousOn h J) : ∃ C, ∀ x, ‖h (f x)‖ ≤ C := by
  obtain ⟨c, hc⟩ := tc_comp_sub_hasCompactSupport hf
  have hcont : Continuous (fun x => h (f x)) :=
    hh.comp_continuous (tc_cont hf) hf.2
  obtain ⟨C, hC⟩ := (hcont.sub continuous_const).bounded_above_of_compact_support (hc h)
  refine ⟨C + ‖h c‖, fun x => ?_⟩
  have := hC x
  simp only [Pi.sub_apply] at this
  calc ‖h (f x)‖ = ‖(h (f x) - h c) + h c‖ := by ring_nf
    _ ≤ ‖h (f x) - h c‖ + ‖h c‖ := norm_add_le _ _
    _ ≤ C + ‖h c‖ := by linarith

lemma tc_integrable_comp {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) (h : ℝ → ℝ)
    (hh : ContinuousOn h J) (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable (fun x => h (f x)) μ := by
  obtain ⟨C, hC⟩ := tc_bounded_comp hf h hh
  exact Integrable.of_bound (hh.comp_continuous (tc_cont hf) hf.2).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

lemma tc_integrable {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J)
    (μ : Measure E) [IsFiniteMeasure μ] : Integrable f μ :=
  tc_integrable_comp hf id continuousOn_id μ

lemma tc_gradient_cont {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    Continuous (gradient f) := by
  have h1 : Continuous (fderiv ℝ f) := (tc_contDiff hf).continuous_fderiv (by simp)
  have : gradient f = fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp h1

lemma tc_gradient_hasCompactSupport {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    HasCompactSupport (gradient f) := by
  obtain ⟨⟨c, g, hg, hgc, rfl⟩, -⟩ := hf
  have h1 : HasCompactSupport (fderiv ℝ (fun x => c + g x)) := by
    have : fderiv ℝ (fun x => c + g x) = fderiv ℝ g := by
      funext x; exact fderiv_const_add (𝕜 := ℝ) (f := g) c
    rw [this]; exact hgc.fderiv (𝕜 := ℝ)
  have : gradient (fun x => c + g x) = fun x =>
      (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun x => c + g x) x) := rfl
  rw [this]
  exact h1.comp_left (by simp)

/-- the energy integrand `Φ''(f) ‖∇f‖²` -/
lemma tc_energy_cont {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    Continuous (fun x => deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2) :=
  ((adm_contOn_d2 hJ hΦ).continuousOn.comp_continuous (tc_cont hf) hf.2).mul
    ((tc_gradient_cont hf).norm.pow 2)

lemma tc_energy_hasCompactSupport {J : Set ℝ} {Φ : ℝ → ℝ} {f : E → ℝ}
    (hf : f ∈ PhiSobBayes.testClass n J) :
    HasCompactSupport (fun x => deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2) := by
  refine (tc_gradient_hasCompactSupport hf).mono ?_
  intro x hx h0
  apply hx; simp [h0]

lemma tc_energy_bounded {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ C, ∀ x, ‖deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2‖ ≤ C :=
  (tc_energy_cont hJ hΦ hf).bounded_above_of_compact_support (tc_energy_hasCompactSupport hf)

lemma tc_energy_integrable {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J)
    (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable (fun x => deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2) μ := by
  obtain ⟨C, hC⟩ := tc_energy_bounded hJ hΦ hf
  exact Integrable.of_bound (tc_energy_cont hJ hΦ hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

lemma tc_energy_nonneg {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {f : E → ℝ}
    (hf : f ∈ PhiSobBayes.testClass n J) (x : E) :
    0 ≤ deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2 :=
  mul_nonneg (hΦ.2.1 _ (hf.2 x)).le (sq_nonneg _)

end PSBC



set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace PSBC

variable {n : ℕ}

lemma bind_postK (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] (t : ℝ)
    (ht : 0 < t) : (PhiSobBayes.gamObs μ t).bind (postK μ t) = μ := by
  ext A hA
  rw [Measure.bind_apply hA (postK μ t).aemeasurable]
  simp_rw [postK_apply]
  exact (PhiSobBayes.eq_46_posterior_averaging μ t ht).2 A hA

lemma lintegral_posterior_avg (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 < t) (G : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y, ∫⁻ x, G x ∂(PhiSobBayes.posterior μ t y) ∂(PhiSobBayes.gamObs μ t) = ∫⁻ x, G x ∂μ := by
  conv_rhs => rw [← bind_postK μ t ht]
  rw [Measure.lintegral_bind (postK μ t).aemeasurable hG.aemeasurable]
  simp_rw [postK_apply]

end PSBC



set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

theorem solution {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : PhiSobBayes.IsLogConcave μ)
    (J : Set ℝ) (hJ : PhiSobBayes.IsOpenInterval J) (Φ : ℝ → ℝ) (hΦ : PhiSobBayes.AdmissiblePhi J Φ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ PhiSobBayes.testClass n J) (t : ℝ) (ht : 0 < t) :
    PhiSobBayes.bayesRisk μ J Φ t f ≤
      ENNReal.ofReal (1 / (2 * t) * ∫ x, deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2 ∂μ) := by
  have hP : IsProbabilityMeasure μ := hμ.1
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun x => deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2
    with hGdef
  have h62 := PhiSobBayes.lemma_6_2 μ J hJ Φ hΦ.1 (PSBC.adm_convex hJ hΦ) f hf.2
    (PSBC.tc_integrable hf μ) (PSBC.tc_integrable_comp hf Φ (PSBC.adm_contOn hΦ) μ) t ht
  rw [h62.2.1]
  apply ENNReal.ofReal_le_ofReal
  -- pointwise bound from Bakry–Émery on the posterior
  have hpt : ∀ y, PhiSobBayes.phiEnt (PhiSobBayes.posterior μ t y) Φ f ≤
      1 / (2 * t) * ∫ x, G x ∂(PhiSobBayes.posterior μ t y) := by
    intro y
    have hslc := PhiSobBayes.lemma_6_1 μ hμ t ht y
    have := (PhiSobBayes.fact_A_22 _ t ht hslc).2.2 J Φ hJ hΦ f hf
    calc _ ≤ 1 / t / 2 * ∫ x, G x ∂(PhiSobBayes.posterior μ t y) := this
      _ = _ := by ring
  have hGnn : ∀ x, 0 ≤ G x := PSBC.tc_energy_nonneg hΦ hf
  have hGint : ∀ (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν], Integrable G ν :=
    fun ν _ => PSBC.tc_energy_integrable hJ hΦ hf ν
  have hGmeas : Measurable G := (PSBC.tc_energy_cont hJ hΦ hf).measurable
  obtain ⟨C, hC⟩ := PSBC.tc_energy_bounded hJ hΦ hf
  -- h y := ∫ G d posterior
  set h : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ∫ x, G x ∂(PhiSobBayes.posterior μ t y) with hh
  have hh_eq : ∀ y, ENNReal.ofReal (h y) = ∫⁻ x, ENNReal.ofReal (G x) ∂(PhiSobBayes.posterior μ t y) :=
    fun y => ofReal_integral_eq_lintegral_ofReal (hGint _) (Filter.Eventually.of_forall hGnn)
  have hh_meas : Measurable h := by
    have : (fun y => ENNReal.ofReal (h y)) = fun y => ∫⁻ x, ENNReal.ofReal (G x) ∂(PSBC.postK μ t y) := by
      funext y; rw [hh_eq, PSBC.postK_apply]
    have hm : Measurable (fun y => ENNReal.ofReal (h y)) := by
      rw [this]; exact (ENNReal.measurable_ofReal.comp hGmeas).lintegral_kernel
    have : h = fun y => (ENNReal.ofReal (h y)).toReal := by
      funext y; rw [ENNReal.toReal_ofReal (integral_nonneg hGnn)]
    rw [this]; exact hm.ennreal_toReal
  have hh_bdd : ∀ y, ‖h y‖ ≤ C := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg hGnn)]
    calc h y ≤ ∫ _x, C ∂(PhiSobBayes.posterior μ t y) :=
          integral_mono (hGint _) (integrable_const _) (fun x => (le_abs_self _).trans (hC x))
      _ = C := by simp
  have hh_int : Integrable h (PhiSobBayes.gamObs μ t) := by
    have : IsProbabilityMeasure (PhiSobBayes.gamObs μ t) := by
      unfold PhiSobBayes.gamObs
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    exact Integrable.of_bound hh_meas.aestronglyMeasurable C (Filter.Eventually.of_forall hh_bdd)
  have hh_total : ∫ y, h y ∂(PhiSobBayes.gamObs μ t) = ∫ x, G x ∂μ := by
    have h1 : ENNReal.ofReal (∫ y, h y ∂(PhiSobBayes.gamObs μ t)) =
        ENNReal.ofReal (∫ x, G x ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hh_int
        (Filter.Eventually.of_forall fun y => integral_nonneg hGnn),
        ofReal_integral_eq_lintegral_ofReal (hGint μ) (Filter.Eventually.of_forall hGnn)]
      simp_rw [hh_eq]
      exact PSBC.lintegral_posterior_avg μ t ht _ (ENNReal.measurable_ofReal.comp hGmeas)
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun y => integral_nonneg hGnn)
      (integral_nonneg hGnn)).1 h1
  by_cases hint : Integrable (fun y => PhiSobBayes.phiEnt (PhiSobBayes.posterior μ t y) Φ f)
      (PhiSobBayes.gamObs μ t)
  · calc ∫ y, PhiSobBayes.phiEnt (PhiSobBayes.posterior μ t y) Φ f ∂(PhiSobBayes.gamObs μ t)
        ≤ ∫ y, 1 / (2 * t) * h y ∂(PhiSobBayes.gamObs μ t) :=
          integral_mono hint (hh_int.const_mul _) hpt
      _ = 1 / (2 * t) * ∫ x, G x ∂μ := by rw [integral_const_mul, hh_total]
  · rw [integral_undef hint]
    exact mul_nonneg (by positivity) (integral_nonneg hGnn)
