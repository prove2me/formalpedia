-- Prove2me | solution 1 for PhiSobBayes.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:32:09.6589+00:00
-- url     : https://prove2.me/submissions/749c05ef-d930-4de2-8633-9a9f37ad1285

import Mathlib
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_phiEnt
import Definitions.Def_PhiSobBayes_bregman
import Definitions.Def_PhiSobBayes_gamJoint
import Definitions.Def_PhiSobBayes_gamObs
import Definitions.Def_PhiSobBayes_posterior
import Definitions.Def_PhiSobBayes_bayesRisk
import Theorems.Thm_PhiSobBayes_eq_46_posterior_averaging
import Theorems.Thm_PhiSobBayes_lemma_A_19

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

noncomputable section

namespace PSB62

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

end PSB62

section A19
open Set

lemma PSB62_support {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) {a b c : ℝ}
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

lemma PSB62_affine {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) :
    ∃ s t : ℝ, ∀ z ∈ J, s * z + t ≤ Φ z := by
  by_cases h : ∃ a ∈ J, ∃ b ∈ J, a < b
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    obtain ⟨s, hs⟩ := PSB62_support hΦ ha hb (c := (a+b)/2) (by linarith) (by linarith)
    exact ⟨s, Φ ((a+b)/2) - s * ((a+b)/2), fun z hz => by have := hs z hz; linarith⟩
  · push Not at h
    rcases J.eq_empty_or_nonempty with hJ | ⟨j, hj⟩
    · exact ⟨0, 0, by simp [hJ]⟩
    · refine ⟨0, Φ j, fun z hz => ?_⟩
      have : z = j := le_antisymm (h j hj z hz) (h z hz j hj)
      subst this; simp

lemma PSB62_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) {f : α → ℝ} (hfJ : ∀ x, f x ∈ J)
    (hf : Integrable f μ) (hΦf : Integrable (fun x => Φ (f x)) μ) :
    (∫ x, f x ∂μ) ∈ J ∧ Φ (∫ x, f x ∂μ) ≤ ∫ x, Φ (f x) ∂μ := by
  set c := ∫ x, f x ∂μ with hc
  by_cases h : ∃ a ∈ J, ∃ b ∈ J, a < c ∧ c < b
  · obtain ⟨a, ha, b, hb, hac, hcb⟩ := h
    refine ⟨hΦ.1.ordConnected.out ha hb ⟨hac.le, hcb.le⟩, ?_⟩
    obtain ⟨s, hs⟩ := PSB62_support hΦ ha hb hac hcb
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

lemma PSB62_meas {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) :
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

lemma PSB62_integral_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (κ : Kernel β α) [IsMarkovKernel κ]
    (g : α → ℝ) (hg : Integrable g (ρ.bind κ)) :
    ∫ x, g x ∂(ρ.bind κ) = ∫ y, ∫ x, g x ∂(κ y) ∂ρ := by
  have := hg
  rw [Measure.comp_eq_comp_const_apply] at this ⊢
  rw [Kernel.integral_comp this]
  simp

lemma PSB62_integrable_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
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

end A19

namespace PSB62

open PhiSobBayes

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

instance gamObs_isProb (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (gamObs μ t) := by
  unfold gamObs
  exact Measure.isProbabilityMeasure_map (Continuous.measurable (by fun_prop)).aemeasurable

instance gamJoint_isProb (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (gamJoint μ t) := by
  unfold gamJoint
  exact Measure.isProbabilityMeasure_map (Continuous.measurable (by fun_prop)).aemeasurable

lemma bind_eq (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (ht : 0 < t) :
    (gamObs μ t).bind (postK μ t) = μ := by
  ext s hs
  rw [Measure.bind_apply hs (postK μ t).measurable.aemeasurable]
  simp_rw [postK_apply]
  exact (eq_46_posterior_averaging μ t ht).2 s hs

lemma gamJoint_eq (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (ht : 0 < t) :
    gamJoint μ t = ((gamObs μ t) ⊗ₘ (postK μ t)).map Prod.swap := by
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    have hA : MeasurableSet A := hA
    have hB : MeasurableSet B := hB
    rw [Measure.map_apply measurable_swap (hA.prod hB), Set.preimage_swap_prod,
      Measure.compProd_apply_prod hB hA]
    simp_rw [postK_apply]
    exact (eq_46_posterior_averaging μ t ht).1 A B hA hB
  · rw [Measure.map_apply measurable_swap MeasurableSet.univ, Set.preimage_univ, measure_univ,
      measure_univ]

lemma lintegral_gamJoint (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (ht : 0 < t)
    (g : E × E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p, g p ∂(gamJoint μ t) = ∫⁻ y, ∫⁻ x, g (x, y) ∂(posterior μ t y) ∂(gamObs μ t) := by
  rw [gamJoint_eq μ t ht, lintegral_map hg measurable_swap,
    Measure.lintegral_compProd (f := fun p => g p.swap) (hg.comp measurable_swap)]
  simp_rw [postK_apply]
  rfl

lemma ae_fst (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) {P : E → Prop}
    (h : ∀ᵐ x ∂μ, P x) : ∀ᵐ p ∂(gamJoint μ t), P p.1 := by
  have hmap : (gamJoint μ t).map Prod.fst = μ := by
    unfold gamJoint
    rw [Measure.map_map measurable_fst (Continuous.measurable (by fun_prop))]
    change (μ.prod (stdGaussian E)).map Prod.fst = μ
    rw [Measure.map_fst_prod]
    simp
  have h' : ∀ᵐ x ∂((gamJoint μ t).map Prod.fst), P x := by rw [hmap]; exact h
  exact ae_of_ae_map measurable_fst.aemeasurable h'

lemma post_le (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (y : E) :
    posterior μ t y ≤ ENNReal.ofReal (1 / Z μ t y) • μ := by
  rw [posterior_eq, ← withDensity_const]
  refine withDensity_mono (Filter.Eventually.of_forall fun x => ?_)
  unfold dens
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (lik_le_one t y x) (Z_pos μ t y).le)

lemma integrable_post (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (y : E) {g : E → ℝ}
    (hg : Integrable g μ) : Integrable g (posterior μ t y) :=
  (hg.smul_measure ENNReal.ofReal_ne_top).mono_measure (post_le μ t y)

lemma ac_post (μ : Measure E) (t : ℝ) (y : E) : posterior μ t y ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma bregman_nonneg {J : Set ℝ} {Φ : ℝ → ℝ} (hΦc : ConvexOn ℝ J Φ)
    (hΦd : ∀ a ∈ J, DifferentiableAt ℝ Φ a) {z a : ℝ} (hz : z ∈ J) (ha : a ∈ J) :
    0 ≤ bregman Φ z a := by
  unfold bregman
  rcases lt_trichotomy z a with h | rfl | h
  · have := hΦc.slope_le_deriv hz ha h (hΦd a ha)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    nlinarith
  · simp
  · have := hΦc.deriv_le_slope ha hz h (hΦd a ha)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith

theorem main (μ : Measure E) [IsProbabilityMeasure μ] (J : Set ℝ) (hJ : J.OrdConnected)
    (Φ : ℝ → ℝ) (hΦc : ConvexOn ℝ J Φ) (hΦd : ∀ a ∈ J, DifferentiableAt ℝ Φ a)
    (f : E → ℝ) (hfJ : ∀ x, f x ∈ J) (hf : Integrable f μ)
    (hΦf : Integrable (fun x => Φ (f x)) μ) (t : ℝ) (ht : 0 < t) :
    let m : E → ℝ := fun y => ∫ x, f x ∂(posterior μ t y)
    (Measurable m ∧ (∀ y, m y ∈ J) ∧
      PhiSobBayes.bayesRisk μ J Φ t f = ∫⁻ p, ENNReal.ofReal (bregman Φ (f p.1) (m p.2)) ∂(gamJoint μ t)) ∧
    PhiSobBayes.bayesRisk μ J Φ t f = ENNReal.ofReal (∫ y, phiEnt (posterior μ t y) Φ f ∂(gamObs μ t)) := by
  intro m
  classical
  have hJm : MeasurableSet J := hJ.measurableSet
  obtain ⟨c, hc⟩ : J.Nonempty := ⟨f 0, hfJ 0⟩
  obtain ⟨f0, hf0m, hf0e⟩ : ∃ f0 : E → ℝ, Measurable f0 ∧ f =ᵐ[μ] f0 :=
    ⟨hf.1.mk f, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
  obtain ⟨f', hf'def⟩ : ∃ f' : E → ℝ, f' = fun x => if f0 x ∈ J then f0 x else c := ⟨_, rfl⟩
  have hf'm : Measurable f' := by
    rw [hf'def]; exact Measurable.ite (hf0m hJm) hf0m measurable_const
  have hf'J : ∀ x, f' x ∈ J := fun x => by
    rw [hf'def]; dsimp only; split_ifs with h
    exacts [h, hc]
  have hff' : f =ᵐ[μ] f' := hf0e.mono fun x hx => by
    rw [hf'def]; dsimp only; rw [if_pos (hx ▸ hfJ x)]; exact hx
  have hΦm : Measurable (J.indicator Φ) := PSB62_meas hΦc
  have hΦcomp : ∀ {α : Type} [MeasurableSpace α] (g : α → ℝ), Measurable g → (∀ x, g x ∈ J) →
      Measurable (fun x => Φ (g x)) := by
    intro α _ g hg hgJ
    have : (fun x => Φ (g x)) = fun x => J.indicator Φ (g x) :=
      funext fun x => (Set.indicator_of_mem (hgJ x) Φ).symm
    rw [this]; exact hΦm.comp hg
  have hΦf'm : Measurable (fun x => Φ (f' x)) := hΦcomp f' hf'm hf'J
  have hf'i : Integrable f' μ := hf.congr hff'
  have hΦf'i : Integrable (fun x => Φ (f' x)) μ :=
    hΦf.congr (hff'.mono fun x hx => by simp only [hx])
  have hpe : ∀ y, f =ᵐ[posterior μ t y] f' := fun y => (ac_post μ t y).ae_le hff'
  have hfi : ∀ y, Integrable f' (posterior μ t y) := fun y => integrable_post μ t y hf'i
  have hΦi : ∀ y, Integrable (fun x => Φ (f' x)) (posterior μ t y) :=
    fun y => integrable_post μ t y hΦf'i
  have hm' : ∀ y, m y = ∫ x, f' x ∂(posterior μ t y) := fun y => integral_congr_ae (hpe y)
  obtain ⟨A, hA⟩ : ∃ A : E → ℝ, ∀ y, A y = ∫ x, Φ (f' x) ∂(posterior μ t y) :=
    ⟨_, fun _ => rfl⟩
  have hEnt : ∀ y, phiEnt (posterior μ t y) Φ f = A y - Φ (m y) := by
    intro y
    rw [hA]
    show ∫ x, Φ (f x) ∂(posterior μ t y) - Φ (m y) = _
    congr 1
    exact integral_congr_ae ((hpe y).mono fun x hx => by simp only [hx])
  have hjen : ∀ y, m y ∈ J ∧ Φ (m y) ≤ A y := fun y => by
    rw [hm', hA]; exact PSB62_jensen (posterior μ t y) hΦc hf'J (hfi y) (hΦi y)
  have hmJ : ∀ y, m y ∈ J := fun y => (hjen y).1
  have hmm : Measurable m := by
    have : m = fun y => ∫ x, f' x ∂(postK μ t y) := by funext y; rw [hm', postK_apply]
    rw [this]; exact (hf'm.stronglyMeasurable.integral_kernel).measurable
  have hAm : Measurable A := by
    have : A = fun y => ∫ x, Φ (f' x) ∂(postK μ t y) := by funext y; rw [hA, postK_apply]
    rw [this]; exact (hΦf'm.stronglyMeasurable.integral_kernel).measurable
  have hbind := bind_eq μ t ht
  have hAi : Integrable A (gamObs μ t) := by
    have := PSB62_integrable_bind (gamObs μ t) (postK μ t) (fun x => Φ (f' x))
      (by rw [hbind]; exact hΦf'i)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [postK_apply, hA]
  have hmi : Integrable m (gamObs μ t) := by
    have := PSB62_integrable_bind (gamObs μ t) (postK μ t) f' (by rw [hbind]; exact hf'i)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [postK_apply]; exact (hm' y).symm
  have hEm : Measurable (fun y => phiEnt (posterior μ t y) Φ f) := by
    have : (fun y => phiEnt (posterior μ t y) Φ f) = fun y => A y - Φ (m y) :=
      funext fun y => hEnt y
    rw [this]; exact hAm.sub (hΦcomp m hmm hmJ)
  have hE0 : ∀ y, 0 ≤ phiEnt (posterior μ t y) Φ f := fun y => by
    rw [hEnt]; linarith [(hjen y).2]
  obtain ⟨s, s0, hs⟩ := PSB62_affine hΦc
  have hEi : Integrable (fun y => phiEnt (posterior μ t y) Φ f) (gamObs μ t) := by
    refine Integrable.mono' (hAi.sub ((hmi.const_mul s).add (integrable_const s0)))
      hEm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hE0 y), hEnt]
    have := hs _ (hjen y).1
    simp only [Pi.sub_apply, Pi.add_apply]
    linarith
  have hinner : ∀ y, ∀ a ∈ J, ∫⁻ x, ENNReal.ofReal (bregman Φ (f' x) a) ∂(posterior μ t y)
      = ENNReal.ofReal (phiEnt (posterior μ t y) Φ f + bregman Φ (m y) a) := by
    intro y a ha
    have hint : Integrable (fun x => bregman Φ (f' x) a) (posterior μ t y) := by
      unfold bregman
      exact ((hΦi y).sub (integrable_const _)).sub
        (((hfi y).sub (integrable_const a)).const_mul _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => bregman_nonneg hΦc hΦd (hf'J x) ha)]
    congr 1
    rw [hEnt, hA, hm']
    unfold bregman
    have i1 : Integrable (fun x => Φ (f' x) - Φ a) (posterior μ t y) :=
      (hΦi y).sub (integrable_const _)
    have i2 : Integrable (fun x => deriv Φ a * (f' x - a)) (posterior μ t y) :=
      ((hfi y).sub (integrable_const a)).const_mul _
    rw [integral_sub i1 i2, integral_sub (hΦi y) (integrable_const _), integral_const_mul,
      integral_sub (hfi y) (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  have hjoint : ∀ h : E → ℝ, Measurable h → (∀ y, h y ∈ J) →
      ∫⁻ p, ENNReal.ofReal (bregman Φ (f p.1) (h p.2)) ∂(gamJoint μ t)
        = ∫⁻ y, ENNReal.ofReal (phiEnt (posterior μ t y) Φ f + bregman Φ (m y) (h y))
            ∂(gamObs μ t) := by
    intro h hh hhJ
    have hae : ∀ᵐ p ∂(gamJoint μ t), ENNReal.ofReal (bregman Φ (f p.1) (h p.2))
        = ENNReal.ofReal (bregman Φ (f' p.1) (h p.2)) := by
      filter_upwards [ae_fst μ t hff'] with p hp
      rw [hp]
    rw [lintegral_congr_ae hae, lintegral_gamJoint μ t ht _ ?_]
    · exact lintegral_congr fun y => hinner y (h y) (hhJ y)
    · refine ENNReal.measurable_ofReal.comp ?_
      unfold bregman
      have h1 : Measurable (fun p : E × E => Φ (h p.2)) :=
        hΦcomp (fun p : E × E => h p.2) (hh.comp measurable_snd) (fun p => hhJ p.2)
      exact ((hΦf'm.comp measurable_fst).sub h1).sub
        (((measurable_deriv Φ).comp (hh.comp measurable_snd)).mul
          ((hf'm.comp measurable_fst).sub (hh.comp measurable_snd)))
  have hlow : ∀ h : E → ℝ, Measurable h → (∀ y, h y ∈ J) →
      ∫⁻ y, ENNReal.ofReal (phiEnt (posterior μ t y) Φ f) ∂(gamObs μ t)
        ≤ ∫⁻ p, ENNReal.ofReal (bregman Φ (f p.1) (h p.2)) ∂(gamJoint μ t) := by
    intro h hh hhJ
    rw [hjoint h hh hhJ]
    exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal
      (le_add_of_nonneg_right (bregman_nonneg hΦc hΦd (hmJ y) (hhJ y)))
  have hatt : ∫⁻ p, ENNReal.ofReal (bregman Φ (f p.1) (m p.2)) ∂(gamJoint μ t)
      = ∫⁻ y, ENNReal.ofReal (phiEnt (posterior μ t y) Φ f) ∂(gamObs μ t) := by
    rw [hjoint m hmm hmJ]
    simp [bregman]
  have hrisk : PhiSobBayes.bayesRisk μ J Φ t f
      = ∫⁻ p, ENNReal.ofReal (bregman Φ (f p.1) (m p.2)) ∂(gamJoint μ t) := by
    unfold PhiSobBayes.bayesRisk
    apply le_antisymm
    · exact iInf_le_of_le m (iInf_le_of_le hmm (iInf_le _ hmJ))
    · rw [hatt]; exact le_iInf fun h => le_iInf fun hh => le_iInf fun hhJ => hlow h hh hhJ
  refine ⟨⟨hmm, hmJ, hrisk⟩, ?_⟩
  rw [hrisk, hatt, ofReal_integral_eq_lintegral_ofReal hEi (Filter.Eventually.of_forall hE0)]

end PSB62

end

open PhiSobBayes in
theorem solution {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (J : Set ℝ) (hJ : IsOpenInterval J) (Φ : ℝ → ℝ) (hΦs : ContDiffOn ℝ ∞ Φ J)
    (hΦc : ConvexOn ℝ J Φ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfJ : ∀ x, f x ∈ J)
    (hf : Integrable f μ) (hΦf : Integrable (fun x => Φ (f x)) μ) (t : ℝ) (ht : 0 < t) :
    let m : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ∫ x, f x ∂(posterior μ t y)
    (Measurable m ∧ (∀ y, m y ∈ J) ∧
      PhiSobBayes.bayesRisk μ J Φ t f = ∫⁻ p, ENNReal.ofReal (bregman Φ (f p.1) (m p.2)) ∂(gamJoint μ t)) ∧
    PhiSobBayes.bayesRisk μ J Φ t f = ENNReal.ofReal (∫ y, phiEnt (posterior μ t y) Φ f ∂(gamObs μ t)) ∧
    ∫ y, phiEnt (posterior μ t y) Φ f ∂(gamObs μ t) = phiEnt μ Φ f - phiEnt (gamObs μ t) Φ m ∧
    (Integrable (fun x => f x ^ 2) μ →
      PhiSobBayes.bayesRisk μ Set.univ (fun z => z ^ 2) t f =
        ENNReal.ofReal (∫ y, variance f (posterior μ t y) ∂(gamObs μ t))) := by
  intro m
  have hΦd : ∀ a ∈ J, DifferentiableAt ℝ Φ a := fun a ha =>
    (hΦs.contDiffAt (hJ.1.mem_nhds ha)).differentiableAt (by simp)
  have hmain := PSB62.main μ J hJ.2.1 Φ hΦc hΦd f hfJ hf hΦf t ht
  refine ⟨hmain.1, hmain.2, ?_, ?_⟩
  · have hbind := PSB62.bind_eq μ t ht
    have := lemma_A_19 (gamObs μ t) (PSB62.postK μ t) J hJ.2.1 Φ hΦc f hfJ
      (by rw [hbind]; exact hf) (by rw [hbind]; exact hΦf)
    rw [hbind] at this
    simp only [PSB62.postK_apply] at this
    exact eq_sub_of_add_eq this.symm
  · intro hf2
    have hmain2 := PSB62.main μ Set.univ Set.ordConnected_univ (fun z => z ^ 2)
      (even_two.convexOn_pow) (fun a _ => by fun_prop) f (fun _ => Set.mem_univ _) hf hf2 t ht
    rw [hmain2.2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hms : AEStronglyMeasurable f (posterior μ t y) := hf.1.mono_ac (PSB62.ac_post μ t y)
    have hL : MemLp f 2 (posterior μ t y) :=
      (memLp_two_iff_integrable_sq hms).2 (PSB62.integrable_post μ t y hf2)
    show phiEnt (posterior μ t y) (fun z => z ^ 2) f = variance f (posterior μ t y)
    rw [variance_eq_sub hL]
    simp [phiEnt]
