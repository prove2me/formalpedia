-- Prove2me | solution 1 for PhiSobBayes.theorem_3_1_forward
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:42:39.709476+00:00
-- url     : https://prove2.me/submissions/f6cce9ca-e4d6-42b7-abc7-aa15d60ad0e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PhiSobBayes_posterior
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_AdmissiblePhi
import Definitions.Def_PhiSobBayes_testClass
import Definitions.Def_PhiSobBayes_phiEnt
import Definitions.Def_PhiSobBayes_PhiSobolev
import Definitions.Def_PhiSobBayes_bayesRisk
import Definitions.Def_PhiSobBayes_bregman
import Definitions.Def_PhiSobBayes_gamJoint
import Definitions.Def_PhiSobBayes_gamObs
import Definitions.Def_PhiSobBayes_phiDiv
import Theorems.Thm_PhiSobBayes_eq_46_posterior_averaging
import Theorems.Thm_PhiSobBayes_lemma_6_2
import Theorems.Thm_PhiSobBayes_fact_A_25

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace PSBF

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

end PSBF

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

noncomputable section

namespace PSBF

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

end PSBF

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace PSBF

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

end PSBF

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

lemma PSBF_A19_support {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) {a b c : ℝ}
    (ha : a ∈ J) (hb : b ∈ J) (hac : a < c) (hcb : c < b) :
    ∃ s : ℝ, ∀ z ∈ J, Φ c + s * (z - c) ≤ Φ z := by
  have hcJ : c ∈ interior J := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Ioo_mem_nhds hac hcb)
      (fun x hx => hΦ.1.ordConnected.out ha hb (Ioo_subset_Icc_self hx))
  refine ⟨derivWithin Φ (Ioi c) c, fun z hz => ?_⟩
  rcases lt_trichotomy z c with hzc | rfl | hzc
  · have h1 := hΦ.slope_le_leftDeriv_of_mem_interior hz hcJ hzc
    have h2 := hΦ.leftDeriv_le_rightDeriv_of_mem_interior hcJ
    have h3 := h1.trans h2
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h3
    nlinarith
  · simp
  · have h1 := hΦ.rightDeriv_le_slope_of_mem_interior hcJ hz hzc
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
    nlinarith

lemma PSBF_A19_affine {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) :
    ∃ s t : ℝ, ∀ z ∈ J, s * z + t ≤ Φ z := by
  by_cases h : ∃ a ∈ J, ∃ b ∈ J, a < b
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    obtain ⟨s, hs⟩ := PSBF_A19_support hΦ ha hb (c := (a+b)/2) (by linarith) (by linarith)
    exact ⟨s, Φ ((a+b)/2) - s * ((a+b)/2), fun z hz => by have := hs z hz; linarith⟩
  · push Not at h
    rcases J.eq_empty_or_nonempty with hJ | ⟨j, hj⟩
    · exact ⟨0, 0, by simp [hJ]⟩
    · refine ⟨0, Φ j, fun z hz => ?_⟩
      have : z = j := le_antisymm (h j hj z hz) (h z hz j hj)
      subst this; simp

lemma PSBF_A19_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) {f : α → ℝ} (hfJ : ∀ x, f x ∈ J)
    (hf : Integrable f μ) (hΦf : Integrable (fun x => Φ (f x)) μ) :
    (∫ x, f x ∂μ) ∈ J ∧ Φ (∫ x, f x ∂μ) ≤ ∫ x, Φ (f x) ∂μ := by
  set c := ∫ x, f x ∂μ with hc
  by_cases h : ∃ a ∈ J, ∃ b ∈ J, a < c ∧ c < b
  · obtain ⟨a, ha, b, hb, hac, hcb⟩ := h
    refine ⟨hΦ.1.ordConnected.out ha hb ⟨hac.le, hcb.le⟩, ?_⟩
    obtain ⟨s, hs⟩ := PSBF_A19_support hΦ ha hb hac hcb
    have hsub : Integrable (fun x => f x - c) μ := hf.sub (integrable_const c)
    have hsub' : Integrable (fun x => s * (f x - c)) μ := hsub.const_mul s
    have hi : Integrable (fun x => Φ c + s * (f x - c)) μ := (integrable_const _).add hsub'
    have h1 : ∫ x, (Φ c + s * (f x - c)) ∂μ = Φ c := by
      rw [integral_add (integrable_const _) hsub', integral_const, integral_const_mul,
        integral_sub hf (integrable_const _), integral_const]
      simp [hc]
    calc Φ c = ∫ x, (Φ c + s * (f x - c)) ∂μ := h1.symm
      _ ≤ ∫ x, Φ (f x) ∂μ := integral_mono hi hΦf (fun x => hs _ (hfJ x))
  · push Not at h
    have key : ∀ᵐ x ∂μ, f x = c := by
      by_cases h' : ∃ a ∈ J, a < c
      · obtain ⟨a, ha, hac⟩ := h'
        have hle : ∀ x, f x ≤ c := fun x => h a ha (f x) (hfJ x) hac
        have : ∫ x, (c - f x) ∂μ = 0 := by
          rw [integral_sub (integrable_const _) hf]; simp [hc]
        rw [integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.2 (hle x))
          ((integrable_const _).sub hf)] at this
        filter_upwards [this] with x hx
        simp only [Pi.zero_apply] at hx; linarith
      · push Not at h'
        have hle : ∀ x, c ≤ f x := fun x => h' (f x) (hfJ x)
        have : ∫ x, (f x - c) ∂μ = 0 := by
          rw [integral_sub hf (integrable_const _)]; simp [hc]
        rw [integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.2 (hle x))
          (hf.sub (integrable_const _))] at this
        filter_upwards [this] with x hx
        simp only [Pi.zero_apply] at hx; linarith
    obtain ⟨x0, hx0⟩ := key.exists
    refine ⟨hx0 ▸ hfJ x0, ?_⟩
    have : ∀ᵐ x ∂μ, Φ (f x) = Φ c := key.mono fun x hx => by rw [hx]
    rw [integral_congr_ae this]
    simp

lemma PSBF_A19_meas {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) :
    Measurable (J.indicator Φ) := by
  have hJm : MeasurableSet J := hΦ.1.ordConnected.measurableSet
  refine measurable_of_Iic fun t => ?_
  have : J.indicator Φ ⁻¹' Iic t
      = {x | x ∈ J ∧ Φ x ≤ t} ∪ {x | x ∉ J ∧ (0:ℝ) ≤ t} := by
    ext x; by_cases hx : x ∈ J <;> simp [hx]
  rw [this]
  refine MeasurableSet.union (hΦ.convex_le t).ordConnected.measurableSet ?_
  by_cases ht : (0:ℝ) ≤ t
  · have : {x : ℝ | x ∉ J ∧ (0:ℝ) ≤ t} = Jᶜ := by ext x; simp [ht]
    rw [this]; exact hJm.compl
  · simp [ht]

lemma PSBF_A19_integral_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (κ : Kernel β α) [IsMarkovKernel κ]
    (g : α → ℝ) (hg : Integrable g (ρ.bind κ)) :
    ∫ x, g x ∂(ρ.bind κ) = ∫ y, ∫ x, g x ∂(κ y) ∂ρ := by
  have := hg
  rw [Measure.comp_eq_comp_const_apply] at this ⊢
  rw [Kernel.integral_comp this]
  simp

lemma PSBF_A19_integrable_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (κ : Kernel β α) [IsMarkovKernel κ]
    (g : α → ℝ) (hg : Integrable g (ρ.bind κ)) :
    Integrable (fun y => ∫ x, g x ∂(κ y)) ρ := by
  have hn := Measure.integrable_integral_norm_of_integrable_comp hg
  have hm : AEStronglyMeasurable (fun y => ∫ x, g x ∂(κ y)) ρ := by
    refine ⟨fun y => ∫ x, hg.1.mk g x ∂(κ y), hg.1.stronglyMeasurable_mk.integral_kernel, ?_⟩
    filter_upwards [Measure.ae_ae_of_ae_comp hg.1.ae_eq_mk] with y hy
    exact integral_congr_ae hy
  refine hn.mono' hm (Filter.Eventually.of_forall fun y => ?_)
  exact norm_integral_le_integral_norm _


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PSBF

lemma PSBF_deriv_affine (F : ℝ → ℝ) (s b r : ℝ) :
    deriv (fun r => F (s * r + b)) r = s * deriv F (s * r + b) := by
  have h1 := deriv_comp_mul_left s (fun u => F (u + b)) r
  have h2 : deriv (fun u => F (u + b)) (s * r) = deriv F (s * r + b) :=
    deriv_comp_add_const (f := F) (a := b) (x := s * r)
  rw [h2, smul_eq_mul] at h1
  exact h1

lemma PSBF_deriv_Psi (Φ : ℝ → ℝ) (s b c : ℝ) :
    deriv (fun r => Φ (s * r + b) - c) = fun r => s * deriv Φ (s * r + b) := by
  funext r
  rw [deriv_sub_const, PSBF_deriv_affine]

lemma PSBF_deriv2_Psi (Φ : ℝ → ℝ) (s b c : ℝ) :
    deriv (deriv (fun r => Φ (s * r + b) - c)) = fun r => s ^ 2 * deriv (deriv Φ) (s * r + b) := by
  rw [PSBF_deriv_Psi]
  funext r
  rw [deriv_const_mul_field']
  beta_reduce
  rw [PSBF_deriv_affine]
  ring

lemma PSBF_isOpenInterval_pre {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) (s b : ℝ)
    (h1 : s * 1 + b ∈ J) :
    PhiSobBayes.IsOpenInterval {r | s * r + b ∈ J} := by
  refine ⟨?_, ?_, ⟨1, h1⟩⟩
  · exact hJ.1.preimage (by fun_prop)
  · have hc : Convex ℝ J := hJ.2.1.convex
    have : Convex ℝ {r | s * r + b ∈ J} := by
      intro x hx y hy α β hα hβ hαβ
      have := hc hx hy hα hβ hαβ
      simp only [smul_eq_mul] at this
      show s * (α * x + β * y) + b ∈ J
      convert this using 1
      linear_combination (-b) * hαβ
    exact this.ordConnected

lemma PSBF_admissible {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) (s b c : ℝ) (hs : 0 < s) :
    PhiSobBayes.AdmissiblePhi {r | s * r + b ∈ J} (fun r => Φ (s * r + b) - c) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ContDiffOn.sub ?_ contDiffOn_const
    exact hΦ.1.comp (by fun_prop : ContDiff ℝ ∞ (fun r : ℝ => s * r + b)).contDiffOn
      (fun r hr => hr)
  · intro r hr
    rw [PSBF_deriv2_Psi]
    exact mul_pos (by positivity) (hΦ.2.1 _ hr)
  · rw [PSBF_deriv2_Psi]
    have hconc := hΦ.2.2
    refine ⟨?_, ?_⟩
    · intro x hx y hy α β hα hβ hαβ
      have := hconc.1 hx hy hα hβ hαβ
      simp only [smul_eq_mul] at this
      show s * (α * x + β * y) + b ∈ J
      convert this using 1
      linear_combination (-b) * hαβ
    · intro x hx y hy α β hα hβ hαβ
      have := hconc.2 hx hy hα hβ hαβ
      simp only [smul_eq_mul] at this ⊢
      have he : s * (α * x + β * y) + b = α * (s * x + b) + β * (s * y + b) := by
        linear_combination (-b) * hαβ
      rw [he, mul_inv, mul_inv, mul_inv]
      have hk : 0 ≤ (s ^ 2)⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hk]


section


variable {n : ℕ}

lemma PSBF_gradient_affine (h : EuclideanSpace ℝ (Fin n) → ℝ) (hd : Differentiable ℝ h) (s b : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun x => s * h x + b) x = s • gradient h x := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have := ((hd x).hasFDerivAt.const_mul s).add_const b
  have e : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (s • gradient h x) =
      s • fderiv ℝ h x := by
    rw [map_smulₛₗ, toDual_gradient]; simp
  rw [e]; exact this

lemma PSBF_testClass_affine {J : Set ℝ} (s b : ℝ) {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : h ∈ PhiSobBayes.testClass n {r | s * r + b ∈ J}) :
    (fun x => s * h x + b) ∈ PhiSobBayes.testClass n J := by
  obtain ⟨⟨c0, g, hg, hgc, rfl⟩, hJ'⟩ := hh
  refine ⟨⟨s * c0 + b, fun x => s * g x, contDiff_const.mul hg, hgc.mul_left, ?_⟩,
    fun x => hJ' x⟩
  funext x; ring

lemma PSBF_phiSobolev {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (C : ℝ) (hS : PhiSobBayes.PhiSobolev μ J Φ C) (s b c : ℝ) :
    PhiSobBayes.PhiSobolev μ {r | s * r + b ∈ J} (fun r => Φ (s * r + b) - c) C := by
  intro h hh
  have hf' := PSBF_testClass_affine s b hh
  have hhint : Integrable h μ := tc_integrable hh μ
  have key1 : PhiSobBayes.phiEnt μ (fun r => Φ (s * r + b) - c) h =
      PhiSobBayes.phiEnt μ Φ (fun x => s * h x + b) := by
    unfold PhiSobBayes.phiEnt
    rw [integral_sub (tc_integrable_comp hf' Φ (adm_contOn hΦ) μ) (integrable_const c),
      integral_add (hhint.const_mul s) (integrable_const b), integral_const_mul]
    simp
  have key2 : ∀ x, deriv (deriv (fun r => Φ (s * r + b) - c)) (h x) * ‖gradient h x‖ ^ 2 =
      deriv (deriv Φ) (s * h x + b) * ‖gradient (fun x => s * h x + b) x‖ ^ 2 := by
    intro x
    rw [PSBF_deriv2_Psi, PSBF_gradient_affine h ((tc_contDiff hh).differentiable (by simp)),
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [key1]
  simp_rw [key2]
  exact hS _ hf'


end

section

variable {n : ℕ}

instance PSBF_gamObs_isProb (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) : IsProbabilityMeasure (PhiSobBayes.gamObs μ t) := by
  unfold PhiSobBayes.gamObs
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance PSBF_gamJoint_isProb (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) : IsProbabilityMeasure (PhiSobBayes.gamJoint μ t) := by
  unfold PhiSobBayes.gamJoint
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma PSBF_gamJoint_rect (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 < t) (A B : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    PhiSobBayes.gamJoint μ t (A ×ˢ B) =
      (((PhiSobBayes.gamObs μ t) ⊗ₘ postK μ t).map Prod.swap) (A ×ˢ B) := by
  rw [Measure.map_apply measurable_swap (hA.prod hB), Set.preimage_swap_prod,
    Measure.compProd_apply_prod hB hA, (PhiSobBayes.eq_46_posterior_averaging μ t ht).1 A B hA hB]
  simp_rw [postK_apply]

lemma PSBF_gamJoint_eq (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 < t) :
    PhiSobBayes.gamJoint μ t = ((PhiSobBayes.gamObs μ t) ⊗ₘ postK μ t).map Prod.swap := by
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact PSBF_gamJoint_rect μ t ht A B hA hB
  · rw [← Set.univ_prod_univ]
    exact PSBF_gamJoint_rect μ t ht _ _ MeasurableSet.univ MeasurableSet.univ

lemma PSBF_gamJoint_lintegral (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 < t)
    (F : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F p ∂(PhiSobBayes.gamJoint μ t) =
      ∫⁻ y, ∫⁻ x, F (x, y) ∂(PhiSobBayes.posterior μ t y) ∂(PhiSobBayes.gamObs μ t) := by
  rw [PSBF_gamJoint_eq μ t ht, lintegral_map hF measurable_swap,
    Measure.lintegral_compProd (f := fun a => F a.swap) (hF.comp measurable_swap)]
  simp_rw [postK_apply]
  rfl

lemma PSBF_gamObs_withDensity (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 < t) (G : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hG : Measurable G) :
    PhiSobBayes.gamObs (μ.withDensity G) t =
      (PhiSobBayes.gamObs μ t).withDensity
        (fun y => ∫⁻ x, G x ∂(PhiSobBayes.posterior μ t y)) := by
  have hH : Measurable (fun y => ∫⁻ x, G x ∂(PhiSobBayes.posterior μ t y)) := by
    have : (fun y => ∫⁻ x, G x ∂(PhiSobBayes.posterior μ t y)) =
        fun y => ∫⁻ x, G x ∂(postK μ t y) := by
      funext y; rw [postK_apply]
    rw [this]; exact hG.lintegral_kernel
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hT : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      Real.sqrt t • p.1 + p.2) := by fun_prop
  have hT2 : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (p.1, Real.sqrt t • p.1 + p.2)) := by fun_prop
  have e1 : ∫⁻ a, φ (Real.sqrt t • a.1 + a.2) ∂((μ.prod (stdGaussian
      (EuclideanSpace ℝ (Fin n)))).withDensity fun z => G z.1) =
      ∫⁻ a, G a.1 * φ (Real.sqrt t • a.1 + a.2) ∂(μ.prod (stdGaussian
      (EuclideanSpace ℝ (Fin n)))) :=
    lintegral_withDensity_eq_lintegral_mul _ (hG.comp measurable_fst) (hφ.comp hT)
  have hL : ∫⁻ y, φ y ∂(PhiSobBayes.gamObs (μ.withDensity G) t) =
      ∫⁻ q, G q.1 * φ q.2 ∂(PhiSobBayes.gamJoint μ t) := by
    unfold PhiSobBayes.gamObs PhiSobBayes.gamJoint
    rw [lintegral_map hφ hT, prod_withDensity_left hG, e1,
      lintegral_map (f := fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        G q.1 * φ q.2) (by fun_prop) hT2]
  have hR : ∫⁻ y, φ y ∂((PhiSobBayes.gamObs μ t).withDensity
      (fun y => ∫⁻ x, G x ∂(PhiSobBayes.posterior μ t y))) =
      ∫⁻ y, ∫⁻ x, G x * φ y ∂(PhiSobBayes.posterior μ t y) ∂(PhiSobBayes.gamObs μ t) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hH hφ]
    congr 1
    funext y
    rw [lintegral_mul_const _ hG]
    rfl
  rw [hL, hR, PSBF_gamJoint_lintegral μ t ht (fun q => G q.1 * φ q.2)
    ((hG.comp measurable_fst).mul (hφ.comp measurable_snd))]


end

section


lemma PSBF_bregman_nonneg {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {z a : ℝ} (hz : z ∈ J) (ha : a ∈ J) :
    0 ≤ Φ z - Φ a - deriv Φ a * (z - a) := by
  have hd : DifferentiableAt ℝ Φ a :=
    (hΦ.1.differentiableOn (by simp) a ha).differentiableAt (hJ.1.mem_nhds ha)
  have hc := adm_convex hJ hΦ
  rcases lt_trichotomy z a with hza | rfl | hza
  · have h := hc.slope_le_deriv hz ha hza hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    nlinarith
  · simp
  · have h := hc.deriv_le_slope ha hz hza hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    nlinarith

lemma PSBF_breg_lintegral {α : Type*} [MeasurableSpace α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) (k : α → ℝ) (hk : Measurable k) (lo hi : ℝ)
    (hlo : lo ∈ J) (hhi : hi ∈ J) (hkb : ∀ x, lo ≤ k x ∧ k x ≤ hi) (a : ℝ) (haJ : a ∈ J)
    (ha : ∫ x, k x ∂ρ = a) :
    ∫⁻ x, ENNReal.ofReal (Φ (k x) - Φ a - deriv Φ a * (k x - a)) ∂ρ =
      ENNReal.ofReal (PhiSobBayes.phiEnt ρ Φ k) ∧ 0 ≤ PhiSobBayes.phiEnt ρ Φ k := by
  have hsub : Set.Icc lo hi ⊆ J := hJ.2.1.out hlo hhi
  have hkJ : ∀ x, k x ∈ J := fun x => hsub (hkb x)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((adm_contOn hΦ).mono hsub)
  have hΦk_meas : Measurable (fun x => Φ (k x)) := by
    have : (fun x => Φ (k x)) = fun x => J.indicator Φ (k x) := by
      funext x; rw [Set.indicator_of_mem (hkJ x)]
    rw [this]; exact (PSBF_A19_meas (adm_convex hJ hΦ)).comp hk
  have hΦk : Integrable (fun x => Φ (k x)) ρ :=
    Integrable.of_bound hΦk_meas.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => hB _ (hkb x))
  have hkint : Integrable k ρ := by
    refine Integrable.of_bound hk.aestronglyMeasurable (|lo| + |hi|)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := (hkb x).1; have := neg_abs_le lo; have := abs_nonneg hi; linarith
    · have := (hkb x).2; have := le_abs_self hi; have := abs_nonneg lo; linarith
  have hint : Integrable (fun x => Φ (k x) - Φ a - deriv Φ a * (k x - a)) ρ :=
    (hΦk.sub (integrable_const _)).sub ((hkint.sub (integrable_const _)).const_mul _)
  have hval : ∫ x, (Φ (k x) - Φ a - deriv Φ a * (k x - a)) ∂ρ = PhiSobBayes.phiEnt ρ Φ k := by
    unfold PhiSobBayes.phiEnt
    have h1 : ∫ x, (Φ (k x) - Φ a - deriv Φ a * (k x - a)) ∂ρ =
        ∫ x, (Φ (k x) - Φ a) ∂ρ - ∫ x, deriv Φ a * (k x - a) ∂ρ :=
      integral_sub (hΦk.sub (integrable_const _)) ((hkint.sub (integrable_const _)).const_mul _)
    have h2 : ∫ x, (Φ (k x) - Φ a) ∂ρ = ∫ x, Φ (k x) ∂ρ - Φ a := by
      rw [integral_sub hΦk (integrable_const _)]; simp
    have h3 : ∫ x, deriv Φ a * (k x - a) ∂ρ = 0 := by
      rw [integral_const_mul, integral_sub hkint (integrable_const _), ha]; simp
    rw [h1, h2, h3, ha]; ring
  have hnn : ∀ x, 0 ≤ Φ (k x) - Φ a - deriv Φ a * (k x - a) :=
    fun x => PSBF_bregman_nonneg hJ hΦ (hkJ x) haJ
  refine ⟨?_, ?_⟩
  · rw [← hval, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  · rw [← hval]; exact integral_nonneg hnn

lemma PSBF_phiDiv_eq {α : Type*} [MeasurableSpace α] (ν ρ : Measure α) (Φ : ℝ → ℝ) (s a : ℝ)
    (hs : s ≠ 0) (k : α → ℝ) (hrn : ∀ᵐ x ∂ρ, (ν.rnDeriv ρ x).toReal = 1 + (k x - a) / s) :
    PhiSobBayes.phiDiv (fun r => Φ (s * r + (a - s)) - Φ a) ν ρ =
      ∫⁻ x, ENNReal.ofReal (Φ (k x) - Φ a - deriv Φ a * (k x - a)) ∂ρ := by
  unfold PhiSobBayes.phiDiv
  rw [PSBF_deriv_Psi]
  apply lintegral_congr_ae
  filter_upwards [hrn] with x hx
  rw [hx]
  have e1 : s * (1 + (k x - a) / s) + (a - s) = k x := by field_simp; ring
  have e2 : s * 1 + (a - s) = a := by ring
  have e3 : s * deriv Φ a * (1 + (k x - a) / s - 1) = deriv Φ a * (k x - a) := by
    field_simp; ring
  rw [e1, e2, e3]

variable {n : ℕ}

lemma PSBF_tc_range {J : Set ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ lo hi : ℝ, lo ∈ J ∧ hi ∈ J ∧ ∀ x, lo ≤ f x ∧ f x ≤ hi := by
  have hJf := hf.2
  obtain ⟨⟨c, g, hg, hgc, hfe⟩, -⟩ := hf
  have hcpt : IsCompact (Set.range f) := by
    have : Set.range f = (fun u => c + u) '' Set.range g := by
      rw [hfe, ← Set.range_comp]; rfl
    rw [this]
    exact (hgc.isCompact_range hg.continuous).image (by fun_prop)
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  obtain ⟨lo, ⟨x0, rfl⟩, hlo⟩ := hcpt.exists_isLeast hne
  obtain ⟨hi, ⟨x1, rfl⟩, hhi⟩ := hcpt.exists_isGreatest hne
  exact ⟨f x0, f x1, hJf x0, hJf x1, fun x => ⟨hlo ⟨x, rfl⟩, hhi ⟨x, rfl⟩⟩⟩

lemma PSBF_integral_bounds {α : Type*} [MeasurableSpace α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    (k : α → ℝ) (hk : Integrable k ρ) (lo hi : ℝ) (hkb : ∀ x, lo ≤ k x ∧ k x ≤ hi) :
    lo ≤ ∫ x, k x ∂ρ ∧ ∫ x, k x ∂ρ ≤ hi := by
  constructor
  · calc lo = ∫ _x, lo ∂ρ := by simp
      _ ≤ _ := integral_mono (integrable_const _) hk (fun x => (hkb x).1)
  · calc ∫ x, k x ∂ρ ≤ ∫ _x, hi ∂ρ := integral_mono hk (integrable_const _) (fun x => (hkb x).2)
      _ = hi := by simp


end

end PSBF

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

theorem solution {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 < C) (J : Set ℝ) (hJ : PhiSobBayes.IsOpenInterval J) (Φ : ℝ → ℝ)
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ)
    (hS : PhiSobBayes.PhiSobolev μ J Φ C) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ PhiSobBayes.testClass n J)
    (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (PhiSobBayes.phiEnt μ Φ f / (1 + C * t)) ≤ PhiSobBayes.bayesRisk μ J Φ t f := by
  obtain ⟨lo, hi, hlo, hhi, hfb⟩ := PSBF.PSBF_tc_range hf
  have hfint : Integrable f μ := PSBF.tc_integrable hf μ
  have hfmeas : Measurable f := (PSBF.tc_cont hf).measurable
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∫ x, f x ∂μ = a := ⟨_, rfl⟩
  have hab := PSBF.PSBF_integral_bounds μ f hfint lo hi hfb
  rw [ha] at hab
  have haJ : a ∈ J := hJ.2.1.out hlo hhi hab
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = |lo| + |a| + 1 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; positivity
  have hsne : s ≠ 0 := hs.ne'
  have hJ' : PhiSobBayes.IsOpenInterval {r | s * r + (a - s) ∈ J} :=
    PSBF.PSBF_isOpenInterval_pre hJ s (a - s) (by convert haJ using 1; ring)
  have hΨ : PhiSobBayes.AdmissiblePhi {r | s * r + (a - s) ∈ J}
      (fun r => Φ (s * r + (a - s)) - Φ a) := PSBF.PSBF_admissible hJ hΦ s (a - s) (Φ a) hs
  have hΨ1 : (fun r => Φ (s * r + (a - s)) - Φ a) 1 = 0 := by
    simp only [mul_one, add_sub_cancel, sub_self]
  have hSΨ : PhiSobBayes.PhiSobolev μ {r | s * r + (a - s) ∈ J}
      (fun r => Φ (s * r + (a - s)) - Φ a) C :=
    PSBF.PSBF_phiSobolev hJ hΦ μ C hS s (a - s) (Φ a)
  -- the density `g`
  have hg_nn : ∀ x, 0 ≤ 1 + (f x - a) / s := by
    intro x
    have h1 : -s ≤ f x - a := by
      have := (hfb x).1; have := neg_abs_le lo; have := le_abs_self a; rw [hs_def]; linarith
    have : -1 ≤ (f x - a) / s := by rw [le_div_iff₀ hs]; linarith
    linarith
  have hgmeas : Measurable (fun x => 1 + (f x - a) / s) := by fun_prop
  have hGm : Measurable (fun x => ENNReal.ofReal (1 + (f x - a) / s)) :=
    ENNReal.measurable_ofReal.comp hgmeas
  have hgint : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ρ],
      Integrable f ρ → Integrable (fun x => 1 + (f x - a) / s) ρ ∧
        ∫ x, (1 + (f x - a) / s) ∂ρ = 1 + (∫ x, f x ∂ρ - a) / s := by
    intro ρ _ hfi
    have hi1 : Integrable (fun x => (f x - a) / s) ρ := (hfi.sub (integrable_const a)).div_const s
    refine ⟨(integrable_const 1).add hi1, ?_⟩
    rw [integral_add (integrable_const 1) hi1, integral_div, integral_sub hfi (integrable_const a)]
    simp
  set ν : Measure (EuclideanSpace ℝ (Fin n)) :=
    μ.withDensity (fun x => ENNReal.ofReal (1 + (f x - a) / s)) with hν_def
  have hνprob : IsProbabilityMeasure ν := by
    constructor
    rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hgint μ hfint).1 (Filter.Eventually.of_forall hg_nn),
      (hgint μ hfint).2, ha]
    simp
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous μ _
  have hrnν : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal = 1 + (f x - a) / s := by
    filter_upwards [Measure.rnDeriv_withDensity μ hGm] with x hx
    rw [hν_def, hx]; exact ENNReal.toReal_ofReal (hg_nn x)
  have hνJ : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal ∈ {r | s * r + (a - s) ∈ J} := by
    filter_upwards [hrnν] with x hx
    rw [hx]
    show s * (1 + (f x - a) / s) + (a - s) ∈ J
    convert hf.2 x using 1
    field_simp; ring
  have hA25 := PhiSobBayes.fact_A_25 μ {r | s * r + (a - s) ∈ J} hJ'
    (fun r => Φ (s * r + (a - s)) - Φ a) hΨ hΨ1 C hSΨ ν hνμ hνJ t ht
  -- Lemma 6.2
  have h62 := PhiSobBayes.lemma_6_2 μ J hJ Φ hΦ.1 (PSBF.adm_convex hJ hΦ) f hf.2 hfint
    (PSBF.tc_integrable_comp hf Φ (PSBF.adm_contOn hΦ) μ) t ht
  obtain ⟨⟨hmmeas, hmJ, -⟩, hR, hdec, -⟩ := h62
  have hmb : ∀ y, lo ≤ ∫ x, f x ∂(PhiSobBayes.posterior μ t y) ∧
      ∫ x, f x ∂(PhiSobBayes.posterior μ t y) ≤ hi := fun y =>
    PSBF.PSBF_integral_bounds _ f (PSBF.tc_integrable hf _) lo hi hfb
  have hmavg : ∫ y, (∫ x, f x ∂(PhiSobBayes.posterior μ t y)) ∂(PhiSobBayes.gamObs μ t) = a := by
    have hbind := PSBF_A19_integral_bind (PhiSobBayes.gamObs μ t) (PSBF.postK μ t) f
      (by rw [PSBF.bind_postK μ t ht]; exact hfint)
    rw [PSBF.bind_postK μ t ht] at hbind
    simp_rw [PSBF.postK_apply] at hbind
    rw [← hbind, ha]
  -- the output density
  have hH : (fun y => ∫⁻ x, ENNReal.ofReal (1 + (f x - a) / s) ∂(PhiSobBayes.posterior μ t y)) =
      fun y => ENNReal.ofReal (1 + (∫ x, f x ∂(PhiSobBayes.posterior μ t y) - a) / s) := by
    funext y
    have h := hgint (PhiSobBayes.posterior μ t y) (PSBF.tc_integrable hf _)
    rw [← h.2, ofReal_integral_eq_lintegral_ofReal h.1 (Filter.Eventually.of_forall hg_nn)]
  have hobs := PSBF.PSBF_gamObs_withDensity μ t ht _ hGm
  rw [hH, ← hν_def] at hobs
  have hrnK : ∀ᵐ y ∂(PhiSobBayes.gamObs μ t),
      ((PhiSobBayes.gamObs ν t).rnDeriv (PhiSobBayes.gamObs μ t) y).toReal =
        1 + (∫ x, f x ∂(PhiSobBayes.posterior μ t y) - a) / s := by
    have hHm : Measurable (fun y => ENNReal.ofReal
        (1 + (∫ x, f x ∂(PhiSobBayes.posterior μ t y) - a) / s)) := by fun_prop
    rw [hobs]
    filter_upwards [Measure.rnDeriv_withDensity (PhiSobBayes.gamObs μ t) hHm] with y hy
    rw [hy]
    refine ENNReal.toReal_ofReal ?_
    have h := hgint (PhiSobBayes.posterior μ t y) (PSBF.tc_integrable hf _)
    rw [← h.2]
    exact integral_nonneg hg_nn
  have hD1 := PSBF.PSBF_breg_lintegral μ hJ hΦ f hfmeas lo hi hlo hhi hfb a haJ ha
  have hD2 := PSBF.PSBF_breg_lintegral (PhiSobBayes.gamObs μ t) hJ hΦ _ hmmeas lo hi hlo hhi hmb
    a haJ hmavg
  rw [PSBF.PSBF_phiDiv_eq ν μ Φ s a hsne f hrnν, hD1.1,
    PSBF.PSBF_phiDiv_eq _ _ Φ s a hsne _ hrnK, hD2.1] at hA25
  have h1ct : 0 < 1 + C * t := by positivity
  rw [← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hD1.2)] at hA25
  rw [hR, hdec]
  apply ENNReal.ofReal_le_ofReal
  have : PhiSobBayes.phiEnt μ Φ f / (1 + C * t) =
      PhiSobBayes.phiEnt μ Φ f - C * t / (1 + C * t) * PhiSobBayes.phiEnt μ Φ f := by
    field_simp; ring
  rw [this]
  linarith
