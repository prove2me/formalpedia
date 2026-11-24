-- Prove2me | solution 1 for PhiSobBayes.lemma_A_19
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:21:47.414807+00:00
-- url     : https://prove2.me/submissions/2da57081-8bae-44e9-997c-966fa2c0bb8f

import Mathlib
import Definitions.Def_PhiSobBayes_phiEnt

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

lemma PSBA19_support {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) {a b c : ℝ}
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

lemma PSBA19_affine {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) :
    ∃ s t : ℝ, ∀ z ∈ J, s * z + t ≤ Φ z := by
  by_cases h : ∃ a ∈ J, ∃ b ∈ J, a < b
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    obtain ⟨s, hs⟩ := PSBA19_support hΦ ha hb (c := (a+b)/2) (by linarith) (by linarith)
    exact ⟨s, Φ ((a+b)/2) - s * ((a+b)/2), fun z hz => by have := hs z hz; linarith⟩
  · push Not at h
    rcases J.eq_empty_or_nonempty with hJ | ⟨j, hj⟩
    · exact ⟨0, 0, by simp [hJ]⟩
    · refine ⟨0, Φ j, fun z hz => ?_⟩
      have : z = j := le_antisymm (h j hj z hz) (h z hz j hj)
      subst this; simp

lemma PSBA19_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) {f : α → ℝ} (hfJ : ∀ x, f x ∈ J)
    (hf : Integrable f μ) (hΦf : Integrable (fun x => Φ (f x)) μ) :
    (∫ x, f x ∂μ) ∈ J ∧ Φ (∫ x, f x ∂μ) ≤ ∫ x, Φ (f x) ∂μ := by
  set c := ∫ x, f x ∂μ with hc
  by_cases h : ∃ a ∈ J, ∃ b ∈ J, a < c ∧ c < b
  · obtain ⟨a, ha, b, hb, hac, hcb⟩ := h
    refine ⟨hΦ.1.ordConnected.out ha hb ⟨hac.le, hcb.le⟩, ?_⟩
    obtain ⟨s, hs⟩ := PSBA19_support hΦ ha hb hac hcb
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

lemma PSBA19_meas {J : Set ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ J Φ) :
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

lemma PSBA19_integral_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (κ : Kernel β α) [IsMarkovKernel κ]
    (g : α → ℝ) (hg : Integrable g (ρ.bind κ)) :
    ∫ x, g x ∂(ρ.bind κ) = ∫ y, ∫ x, g x ∂(κ y) ∂ρ := by
  have := hg
  rw [Measure.comp_eq_comp_const_apply] at this ⊢
  rw [Kernel.integral_comp this]
  simp

lemma PSBA19_integrable_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
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

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (κ : Kernel β α) [IsMarkovKernel κ]
    (J : Set ℝ) (hJ : J.OrdConnected) (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ J Φ)
    (f : α → ℝ) (hfJ : ∀ x, f x ∈ J) (hf : Integrable f (ρ.bind κ))
    (hΦf : Integrable (fun x => Φ (f x)) (ρ.bind κ)) :
    PhiSobBayes.phiEnt (ρ.bind κ) Φ f =
      ∫ y, PhiSobBayes.phiEnt (κ y) Φ f ∂ρ
        + PhiSobBayes.phiEnt ρ Φ (fun y => ∫ x, f x ∂(κ y)) := by
  unfold PhiSobBayes.phiEnt
  set H : β → ℝ := fun y => ∫ x, f x ∂(κ y) with hH
  set A : β → ℝ := fun y => ∫ x, Φ (f x) ∂(κ y) with hA
  have hHi : Integrable H ρ := PSBA19_integrable_bind ρ κ f hf
  have hAi : Integrable A ρ := PSBA19_integrable_bind ρ κ _ hΦf
  have hjen : ∀ᵐ y ∂ρ, H y ∈ J ∧ Φ (H y) ≤ A y := by
    filter_upwards [Measure.ae_integrable_of_integrable_comp hf,
      Measure.ae_integrable_of_integrable_comp hΦf] with y h1 h2
    exact PSBA19_jensen (κ y) hΦ hfJ h1 h2
  obtain ⟨s, t, hst⟩ := PSBA19_affine hΦ
  have hΦH : Integrable (fun y => Φ (H y)) ρ := by
    have hm : AEStronglyMeasurable (fun y => Φ (H y)) ρ := by
      have h1 : AEStronglyMeasurable (fun y => J.indicator Φ (H y)) ρ :=
        ((PSBA19_meas hΦ).comp_aemeasurable hHi.1.aemeasurable).aestronglyMeasurable
      refine h1.congr ?_
      filter_upwards [hjen] with y hy
      simp [Set.indicator_of_mem hy.1]
    refine Integrable.mono' ((hAi.norm.add ((hHi.const_mul s).add
      (integrable_const t)).norm)) hm ?_
    filter_upwards [hjen] with y hy
    have l := hst _ hy.1
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_le]
    constructor
    · have := neg_abs_le (s * H y + t)
      have := abs_nonneg (A y)
      linarith
    · have := le_abs_self (A y)
      have := abs_nonneg (s * H y + t)
      linarith
  rw [PSBA19_integral_bind ρ κ _ hΦf, PSBA19_integral_bind ρ κ _ hf]
  rw [integral_sub hAi hΦH]
  ring
