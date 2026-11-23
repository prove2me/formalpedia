-- Prove2me | solution 1 for OneTrap.Core.lemma_B_12
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T02:29:11.159637+00:00
-- url     : https://prove2.me/submissions/bf164fdf-45a6-4170-8cbb-7c21b8ae9d51

import Mathlib
open MeasureTheory
namespace OneTrap.Core

lemma pw_layer (x r1 r2 : ℝ) (h : r1 < r2) :
    max (x - r1) 0 - max (x - r2) 0 = ∫ s in r1..r2, (if s < x then (1:ℝ) else 0) := by
  rw [intervalIntegral.integral_of_le h.le]
  have : ∀ s, (if s < x then (1:ℝ) else 0) = Set.indicator (Set.Iio x) (fun _ => (1:ℝ)) s := by
    intro s; simp [Set.indicator_apply]
  simp_rw [this]
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real]
  rcases le_or_gt x r1 with h1 | h1
  · have : Set.Iio x ∩ Set.Ioc r1 r2 = ∅ := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
      intro ⟨a, b, _⟩; linarith
    rw [this, max_eq_right (by linarith), max_eq_right (by linarith)]; simp
  rcases le_or_gt x r2 with h2 | h2
  · have : Set.Iio x ∩ Set.Ioc r1 r2 = Set.Ioo r1 x := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨a, b, _⟩; exact ⟨b, a⟩
      · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩
    rw [this, max_eq_left (by linarith), max_eq_right (by linarith)]; simp [h1.le]
  · have : Set.Iio x ∩ Set.Ioc r1 r2 = Set.Ioc r1 r2 := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc]
      constructor
      · rintro ⟨_, b⟩; exact b
      · rintro ⟨a, b⟩; exact ⟨by linarith, a, b⟩
    rw [this, max_eq_left (by linarith), max_eq_left (by linarith)]; simp [h.le]


lemma hint_max {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) (r : ℝ) :
    Integrable (fun ω => max (X ω - r) 0) μ := by
  refine Integrable.mono' ((hXint.norm).add (integrable_const |r|)) ?_ ?_
  · exact ((hXint.1.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const)
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_le]; constructor
    · have := abs_nonneg (X ω); have := abs_nonneg r; have := le_max_right (X ω - r) 0; linarith
    · rcases max_cases (X ω - r) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
      · have := le_abs_self (X ω); have := neg_abs_le r; linarith
      · have := abs_nonneg (X ω); have := abs_nonneg r; linarith

lemma layer_meas {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) (hX : Measurable X) (r₁ r₂ : ℝ) (h : r₁ < r₂) :
    (∫ ω, max (X ω - r₁) 0 ∂μ) - (∫ ω, max (X ω - r₂) 0 ∂μ) =
        ∫ s in r₁..r₂, (μ {ω | s < X ω}).toReal := by
  rw [← integral_sub (hint_max μ X hXint r₁) (hint_max μ X hXint r₂)]
  simp_rw [pw_layer _ r₁ r₂ h]
  rw [intervalIntegral.integral_of_le h.le]
  have hm : MeasurableSet {p : Ω × ℝ | p.2 < X p.1} :=
    measurableSet_lt measurable_snd (hX.comp measurable_fst)
  have hg : ∀ ω s, (if s < X ω then (1:ℝ) else 0) = Set.indicator {p : Ω × ℝ | p.2 < X p.1} 1 (ω, s) := by
    intro ω s; simp [Set.indicator_apply]
  simp_rw [intervalIntegral.integral_of_le h.le, hg]
  rw [integral_integral_swap]
  · refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    have : (fun ω => Set.indicator {p : Ω × ℝ | p.2 < X p.1} (1 : Ω × ℝ → ℝ) (ω, s)) =
        Set.indicator {ω | s < X ω} (fun _ => (1:ℝ)) := by
      ext ω; simp [Set.indicator_apply]
    rw [this, integral_indicator_const _ (measurableSet_lt measurable_const hX)]
    simp [Measure.real]
  · refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (measurable_one.indicator hm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, Set.indicator_apply]
      split_ifs <;> simp

lemma layer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) (r₁ r₂ : ℝ) (h : r₁ < r₂) :
    (∫ ω, max (X ω - r₁) 0 ∂μ) - (∫ ω, max (X ω - r₂) 0 ∂μ) =
        ∫ s in r₁..r₂, (μ {ω | s < X ω}).toReal := by
  set Y := hXint.1.mk X with hY
  have hXY : X =ᵐ[μ] Y := hXint.1.ae_eq_mk
  have hYm : Measurable Y := hXint.1.stronglyMeasurable_mk.measurable
  have hYi : Integrable Y μ := hXint.congr hXY
  have e := layer_meas μ Y hYi hYm r₁ r₂ h
  have c : ∀ r : ℝ, ∫ ω, max (X ω - r) 0 ∂μ = ∫ ω, max (Y ω - r) 0 ∂μ := fun r =>
    integral_congr_ae (hXY.mono fun ω hω => by simp [hω])
  have d : ∀ s : ℝ, μ {ω | s < X ω} = μ {ω | s < Y ω} := fun s =>
    measure_congr (hXY.mono fun ω hω => by change (s < X ω) = (s < Y ω); rw [hω] : {ω | s < X ω} =ᵐ[μ] {ω | s < Y ω})
  rw [c, c, e]
  simp_rw [d]


lemma phi_lip {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) :
    LipschitzWith 1 (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, ← integral_sub (hint_max μ X hXint a) (hint_max μ X hXint b)]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := |a - b|)
    (f := fun ω => max (X ω - a) 0 - max (X ω - b) 0)
    (Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs]
      rw [abs_le]; constructor <;>
      · rcases max_cases (X ω - a) 0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases max_cases (X ω - b) 0 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h1, h3] <;>
        (have := le_abs_self (a - b); have := neg_abs_le (a - b); linarith))
  simpa [Measure.real] using this

lemma phi_anti {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) :
    Antitone (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ) := by
  intro a b hab
  exact integral_mono (hint_max μ X hXint b) (hint_max μ X hXint a)
    (fun ω => max_le_max (by linarith) le_rfl)

lemma phi_zero_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (r : ℝ) (h : μ {ω | r < X ω} = 0) : ∫ ω, max (X ω - r) 0 ∂μ = 0 := by
  have : ∀ᵐ ω ∂μ, max (X ω - r) 0 = 0 := by
    have : ∀ᵐ ω ∂μ, ¬ (r < X ω) := by
      rw [ae_iff]; simpa using h
    filter_upwards [this] with ω hω
    exact max_eq_right (by linarith [not_lt.1 hω])
  rw [integral_congr_ae this]; simp

lemma exists_root {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω) (c : ℝ) (hc : 0 < c) :
    ∃ r : ℝ, (∫ ω, max (X ω - r) 0 ∂μ) = c := by
  set φ := fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ with hφ
  have hcont : Continuous φ := (phi_lip μ X hXint).continuous
  have hlow : φ (∫ ω, X ω ∂μ - c) ≥ c := by
    have : ∫ ω, (X ω - (∫ ω, X ω ∂μ - c)) ∂μ ≤ φ (∫ ω, X ω ∂μ - c) :=
      integral_mono (hXint.sub (integrable_const _)) (hint_max μ X hXint _)
        (fun ω => le_max_left _ _)
    rw [integral_sub hXint (integrable_const _)] at this
    simp at this; linarith
  have hlim : Filter.Tendsto φ Filter.atTop (nhds 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ)
      (F := fun (r : ℝ) ω => max (X ω - r) 0) (f := fun _ => (0:ℝ)) (l := Filter.atTop)
      (bound := fun ω => X ω)
      (Filter.Eventually.of_forall fun r => ((hXint.1.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const))
      (by
        filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with r hr
        filter_upwards [hXnonneg] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) hω)
      hXint
      (Filter.Eventually.of_forall fun ω => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop (X ω)] with r hr
        exact (max_eq_right (by linarith)).symm)
    simpa using this
  obtain ⟨b, hb⟩ := (hlim.eventually (gt_mem_nhds hc)).exists_forall_of_atTop
  have hb' : φ (max b (∫ ω, X ω ∂μ - c) + 1) < c := hb _ (by
    exact le_trans (le_max_left _ _) (by linarith))
  set a := ∫ ω, X ω ∂μ - c
  have hab : a ≤ max b a + 1 := by linarith [le_max_right b a]
  have := intermediate_value_Icc' hab hcont.continuousOn ⟨hb'.le, hlow⟩
  obtain ⟨r, _, hr⟩ := this
  exact ⟨r, hr⟩

lemma uniq_root {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) (c : ℝ) (hc : 0 < c) (r₁ r₂ : ℝ) (h : r₁ < r₂)
    (h1 : ∫ ω, max (X ω - r₁) 0 ∂μ = c) (h2 : ∫ ω, max (X ω - r₂) 0 ∂μ = c) : False := by
  have hl := layer μ X hXint r₁ r₂ h
  rw [h1, h2, sub_self] at hl
  have hp : 0 < (μ {ω | r₂ < X ω}).toReal := by
    have : μ {ω | r₂ < X ω} ≠ 0 := fun h0 => by
      have := phi_zero_iff μ X r₂ h0; linarith
    exact ENNReal.toReal_pos this (measure_ne_top _ _)
  have hanti : Antitone (fun s : ℝ => (μ {ω | s < X ω}).toReal) := by
    intro a b hab
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
    exact lt_of_le_of_lt hab hω
  have hint := hanti.intervalIntegrable (μ := volume) (a := r₁) (b := r₂)
  have := intervalIntegral.integral_mono_on h.le (intervalIntegrable_const (μ := volume) (c := (μ {ω | r₂ < X ω}).toReal))
    hint (fun s hs => hanti hs.2)
  rw [← hl] at this
  simp at this
  nlinarith

lemma ess_part {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) :
    IsLeast {r : EReal | ∫⁻ ω, (((X ω : ℝ) : EReal) - r).toENNReal ∂μ = 0}
      (essSup (fun ω => ((X ω : ℝ) : EReal)) μ) := by
  have key : ∀ r : EReal, (∫⁻ ω, (((X ω : ℝ) : EReal) - r).toENNReal ∂μ = 0) ↔
      ∀ᵐ ω ∂μ, ((X ω : ℝ) : EReal) ≤ r := by
    intro r
    have hm : AEMeasurable (fun ω => (((X ω : ℝ) : EReal) - r).toENNReal) μ := by
      have : AEMeasurable (fun ω => ((X ω : ℝ) : EReal)) μ :=
        measurable_coe_real_ereal.comp_aemeasurable hXint.1.aemeasurable
      exact measurable_ereal_toENNReal.comp_aemeasurable (this.sub_const r)
    rw [lintegral_eq_zero_iff' hm]
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.zero_apply]
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
  constructor
  · rw [Set.mem_ofPred_eq, key]; exact ae_le_essSup (by isBoundedDefault)
  · intro r hr
    rw [Set.mem_ofPred_eq, key] at hr
    exact essSup_le_of_ae_le _ hr

theorem lemma_B_12_aux {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    (Continuous (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ) ∧
      Antitone (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ) ∧
      LipschitzWith 1 (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ)) ∧
    (∀ r₁ r₂ : ℝ, r₁ < r₂ →
      (∫ ω, max (X ω - r₁) 0 ∂μ) - (∫ ω, max (X ω - r₂) 0 ∂μ) =
        ∫ s in r₁..r₂, (μ {ω | s < X ω}).toReal) ∧
    (∀ c : ℝ, 0 < c → ∃! r : ℝ, (∫ ω, max (X ω - r) 0 ∂μ) = c) ∧
    IsLeast {r : EReal | ∫⁻ ω, (((X ω : ℝ) : EReal) - r).toENNReal ∂μ = 0}
      (essSup (fun ω => ((X ω : ℝ) : EReal)) μ) := by
  refine ⟨⟨(phi_lip μ X hXint).continuous, phi_anti μ X hXint, phi_lip μ X hXint⟩,
    layer μ X hXint, fun c hc => ?_, ess_part μ X hXint⟩
  obtain ⟨r, hr⟩ := exists_root μ X hXint hXnonneg c hc
  refine ⟨r, hr, fun r' hr' => ?_⟩
  rcases lt_trichotomy r' r with h | h | h
  · exact (uniq_root μ X hXint c hc r' r h hr' hr).elim
  · exact h
  · exact (uniq_root μ X hXint c hc r r' h hr hr').elim

end OneTrap.Core

open MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    (Continuous (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ) ∧
      Antitone (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ) ∧
      LipschitzWith 1 (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ)) ∧
    (∀ r₁ r₂ : ℝ, r₁ < r₂ →
      (∫ ω, max (X ω - r₁) 0 ∂μ) - (∫ ω, max (X ω - r₂) 0 ∂μ) =
        ∫ s in r₁..r₂, (μ {ω | s < X ω}).toReal) ∧
    (∀ c : ℝ, 0 < c → ∃! r : ℝ, (∫ ω, max (X ω - r) 0 ∂μ) = c) ∧
    IsLeast {r : EReal | ∫⁻ ω, (((X ω : ℝ) : EReal) - r).toENNReal ∂μ = 0}
      (essSup (fun ω => ((X ω : ℝ) : EReal)) μ) := OneTrap.Core.lemma_B_12_aux μ X hXint hXnonneg
