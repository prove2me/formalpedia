-- Prove2me | solution 1 for SampleDrivenOS.Structure.eq_8_moved_feasible
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:58:42.546676+00:00
-- url     : https://prove2.me/submissions/b185280f-67e3-402b-9df0-e00d0a1d3a23

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SDOSEq8
open SampleDrivenOS.Structure

variable {p : ℝ} {q : ℝ → ℕ → ℝ}

lemma cumMass_le_one (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) : cumMass p q t ≤ 1 := by
  have := hq.2.2 t ht 1 le_rfl
  exact le_trans le_add_self this

lemma cumMass_mono (p : ℝ) (q : ℝ → ℕ → ℝ) : Monotone (cumMass p q) := by
  intro a b hab
  unfold cumMass
  exact lintegral_mono_set (Icc_subset_Icc_right hab)

lemma envelope_measurable (p : ℝ) (q : ℝ → ℕ → ℝ) : Measurable (envelope p q) := by
  unfold envelope
  have h1 : Measurable (fun t : ℝ => (cumMass p q t).toReal) :=
    ENNReal.measurable_toReal.comp (cumMass_mono p q).measurable
  exact (measurable_const.div measurable_id).mul (measurable_const.sub h1)

lemma toReal_cumMass_le_one (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) :
    (cumMass p q t).toReal ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (cumMass_le_one hq ht)
  simpa using this

lemma envelope_nonneg (hp0 : 0 ≤ p) (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) :
    0 ≤ envelope p q t := by
  unfold envelope
  have h1 := toReal_cumMass_le_one hq ht
  have h2 : 0 ≤ t := le_trans hp0 ht.1
  have : 0 ≤ 1 / t := by positivity
  exact mul_nonneg this (by linarith)

lemma envelope_le (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) (ht0 : 0 < t) :
    envelope p q t ≤ 1 / t := by
  unfold envelope
  have h0 : 0 ≤ (cumMass p q t).toReal := ENNReal.toReal_nonneg
  have : 0 < 1 / t := by positivity
  have h1 := toReal_cumMass_le_one hq ht
  calc 1 / t * (1 - (cumMass p q t).toReal) ≤ 1 / t * 1 := by
        apply mul_le_mul_of_nonneg_left _ this.le; linarith
    _ = 1 / t := by ring

lemma q_le_envelope (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) (ht0 : 0 < t)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : q t ℓ ≤ envelope p q t := by
  have hf := hq.2.2 t ht ℓ hℓ
  have hqn : 0 ≤ q t ℓ := hq.1 t ht ℓ hℓ
  have hM : cumMass p q t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (cumMass_le_one hq ht)
  have hA : ENNReal.ofReal (t * q t ℓ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono ENNReal.one_ne_top hf
  rw [ENNReal.toReal_add hA hM, ENNReal.toReal_ofReal (by positivity)] at h2
  simp only [ENNReal.toReal_one] at h2
  unfold envelope
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ht0]
  linarith

lemma nbTerm_continuous (k ℓ : ℕ) : Continuous (nbTerm k ℓ) := by
  unfold nbTerm
  fun_prop

lemma nbTerm_nonneg (k ℓ : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ nbTerm k ℓ t := by
  unfold nbTerm
  apply Finset.sum_nonneg
  intro j _
  have : 0 ≤ 1 - t := by linarith [ht.2]
  have : 0 ≤ t := ht.1
  positivity


lemma ofReal_one_sub_add {x : ENNReal} (hx : x ≤ 1) : ENNReal.ofReal (1 - x.toReal) + x = 1 := by
  have hxt : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx
  have h1 : x.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hx; simpa using this
  calc ENNReal.ofReal (1 - x.toReal) + x
      = ENNReal.ofReal (1 - x.toReal) + ENNReal.ofReal x.toReal := by
        rw [ENNReal.ofReal_toReal hxt]
    _ = ENNReal.ofReal (1 - x.toReal + x.toReal) := by
        rw [ENNReal.ofReal_add (by linarith) ENNReal.toReal_nonneg]
    _ = 1 := by simp

lemma moved_measurable (p : ℝ) (q : ℝ → ℕ → ℝ) (tl : ℕ → ℝ) (ℓ : ℕ) :
    Measurable (fun τ => movedSolution p q tl τ ℓ) := by
  unfold movedSolution
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    (envelope_measurable p q) measurable_const

lemma hII {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : IntegrableOn f (Icc a b)) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 h

lemma envelope_integrableOn (hp0 : 0 ≤ p) (hq : IsFeasible p q) {s : ℝ} (hs : s ∈ Icc p 1)
    (hs0 : 0 < s) {a b : ℝ} (hsa : s ≤ a) (hb : b ≤ 1) : IntegrableOn (envelope p q) (Icc a b) := by
  refine Measure.integrableOn_of_bounded (M := 1 / s) (measure_Icc_lt_top.ne)
    (envelope_measurable p q).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  have ht' : t ∈ Icc p 1 := ⟨le_trans hs.1 (le_trans hsa ht.1), le_trans ht.2 hb⟩
  have hst : s ≤ t := le_trans hsa ht.1
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  rw [Real.norm_eq_abs, abs_of_nonneg (envelope_nonneg hp0 hq ht')]
  calc envelope p q t ≤ 1 / t := envelope_le hq ht' ht0
    _ ≤ 1 / s := one_div_le_one_div_of_le hs0 hst

/-- Real comparison: the mass of the moved component up to `τ` is at most that of `q`. -/
lemma real_mass_le (hp0 : 0 ≤ p) (hq : IsFeasible p q) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {s : ℝ}
    (hs : s ∈ Icc p 1) (hs0 : 0 < s)
    (hmass : ∫ τ in p..1, q τ ℓ = ∫ τ in s..1, envelope p q τ) {τ : ℝ} (hsτ : s ≤ τ)
    (hτ1 : τ ≤ 1) :
    ∫ σ in Icc s τ, envelope p q σ ≤ ∫ σ in Icc p τ, q σ ℓ := by
  have hpτ : p ≤ τ := le_trans hs.1 hsτ
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsτ,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpτ]
  have hqint : IntegrableOn (fun t => q t ℓ) (Icc p 1) := hq.2.1 ℓ hℓ
  have hq1 : IntervalIntegrable (fun t => q t ℓ) volume p τ :=
    hII hpτ (hqint.mono_set (Icc_subset_Icc_right hτ1))
  have hq2 : IntervalIntegrable (fun t => q t ℓ) volume τ 1 :=
    hII hτ1 (hqint.mono_set (Icc_subset_Icc_left hpτ))
  have hG1 : IntervalIntegrable (envelope p q) volume s τ :=
    hII hsτ (envelope_integrableOn hp0 hq hs hs0 le_rfl hτ1)
  have hG2 : IntervalIntegrable (envelope p q) volume τ 1 :=
    hII hτ1 (envelope_integrableOn hp0 hq hs hs0 hsτ le_rfl)
  have e1 := intervalIntegral.integral_add_adjacent_intervals hq1 hq2
  have e2 := intervalIntegral.integral_add_adjacent_intervals hG1 hG2
  have hle : ∫ t in τ..1, q t ℓ ≤ ∫ t in τ..1, envelope p q t := by
    apply intervalIntegral.integral_mono_on hτ1 hq2 hG2
    intro t ht
    exact q_le_envelope hq ⟨le_trans hpτ ht.1, ht.2⟩ (lt_of_lt_of_le hs0 (le_trans hsτ ht.1)) hℓ
  linarith

/-- The key ENNReal comparison behind (8): the moved solution never has more cumulative
mass than `q`. -/
lemma lmass_le (hp0 : 0 ≤ p) (hq : IsFeasible p q) (tl : ℕ → ℝ)
    (htl : ∀ ℓ : ℕ, 1 ≤ ℓ → tl ℓ ∈ Icc p 1) (htl0 : ∀ ℓ : ℕ, 1 ≤ ℓ → 0 < tl ℓ)
    (hmass : ∀ ℓ : ℕ, 1 ≤ ℓ → ∫ τ in p..1, q τ ℓ = ∫ τ in (tl ℓ)..1, envelope p q τ)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {τ : ℝ} (hτ : τ ∈ Icc p 1) :
    ∫⁻ σ in Icc p τ, ENNReal.ofReal (movedSolution p q tl σ ℓ) ≤
      ∫⁻ σ in Icc p τ, ENNReal.ofReal (q σ ℓ) := by
  set s := tl ℓ with hs_def
  have hs := htl ℓ hℓ
  have hs0 := htl0 ℓ hℓ
  have hqint : IntegrableOn (fun t => q t ℓ) (Icc p τ) :=
    (hq.2.1 ℓ hℓ).mono_set (Icc_subset_Icc_right hτ.2)
  have hrhs : ∫⁻ σ in Icc p τ, ENNReal.ofReal (q σ ℓ) =
      ENNReal.ofReal (∫ σ in Icc p τ, q σ ℓ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hqint]
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => hq.1 t ⟨ht.1, le_trans ht.2 hτ.2⟩ ℓ hℓ)
  have hL : ∫⁻ σ in Icc p τ, ENNReal.ofReal (movedSolution p q tl σ ℓ) =
      ∫⁻ σ in Icc p τ ∩ Ici s, ENNReal.ofReal (envelope p q σ) := by
    have : (fun σ => ENNReal.ofReal (movedSolution p q tl σ ℓ)) =
        (Ici s).indicator (fun σ => ENNReal.ofReal (envelope p q σ)) := by
      funext σ
      by_cases h : s ≤ σ
      · have h' : tl ℓ ≤ σ := by rw [← hs_def]; exact h
        simp [movedSolution, h', indicator, h]
      · have h' : ¬ tl ℓ ≤ σ := by rw [← hs_def]; exact h
        simp [movedSolution, h', indicator, h]
    rw [this, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_comm]
  rw [hL, hrhs]
  by_cases hsτ : s ≤ τ
  · calc ∫⁻ σ in Icc p τ ∩ Ici s, ENNReal.ofReal (envelope p q σ)
        ≤ ∫⁻ σ in Icc s τ, ENNReal.ofReal (envelope p q σ) := by
          apply lintegral_mono_set
          intro x hx; exact ⟨hx.2, hx.1.2⟩
      _ = ENNReal.ofReal (∫ σ in Icc s τ, envelope p q σ) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            (envelope_integrableOn hp0 hq hs hs0 le_rfl hτ.2)]
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
          exact Filter.Eventually.of_forall (fun t ht =>
            envelope_nonneg hp0 hq ⟨le_trans hs.1 ht.1, le_trans ht.2 hτ.2⟩)
      _ ≤ ENNReal.ofReal (∫ σ in Icc p τ, q σ ℓ) := by
          apply ENNReal.ofReal_le_ofReal
          exact real_mass_le hp0 hq hℓ hs hs0 (hmass ℓ hℓ) hsτ hτ.2
  · have : Icc p τ ∩ Ici s = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Ici, mem_empty_iff_false, iff_false]
      intro ⟨⟨_, h2⟩, h3⟩; exact hsτ (le_trans h3 h2)
    rw [this]; simp

lemma cumMass_moved_le (hp0 : 0 ≤ p) (hq : IsFeasible p q) (tl : ℕ → ℝ)
    (htl : ∀ ℓ : ℕ, 1 ≤ ℓ → tl ℓ ∈ Icc p 1) (htl0 : ∀ ℓ : ℕ, 1 ≤ ℓ → 0 < tl ℓ)
    (hmass : ∀ ℓ : ℕ, 1 ≤ ℓ → ∫ τ in p..1, q τ ℓ = ∫ τ in (tl ℓ)..1, envelope p q τ)
    {τ : ℝ} (hτ : τ ∈ Icc p 1) :
    cumMass p (movedSolution p q tl) τ ≤ cumMass p q τ := by
  unfold cumMass
  rw [lintegral_tsum, lintegral_tsum]
  · apply ENNReal.tsum_le_tsum
    intro s
    exact lmass_le hp0 hq tl htl htl0 hmass (by omega) hτ
  · intro s
    have : IntegrableOn (fun t => q t (s + 1)) (Icc p τ) :=
      (hq.2.1 (s + 1) (by omega)).mono_set (Icc_subset_Icc_right hτ.2)
    exact this.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  · intro s
    exact ((moved_measurable p q tl (s + 1)).ennreal_ofReal).aemeasurable

end SDOSEq8

open SampleDrivenOS.Structure in
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (q : ℝ → ℕ → ℝ)
    (hq : IsFeasible p q) (tl : ℕ → ℝ) (htl : ∀ ℓ : ℕ, 1 ≤ ℓ → tl ℓ ∈ Icc p 1)
    (htl0 : ∀ ℓ : ℕ, 1 ≤ ℓ → 0 < tl ℓ)
    (hmass : ∀ ℓ : ℕ, 1 ≤ ℓ → ∫ τ in p..1, q τ ℓ = ∫ τ in (tl ℓ)..1, envelope p q τ) :
    IsFeasible p (movedSolution p q tl) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∫ τ in p..1, movedSolution p q tl τ ℓ = ∫ τ in p..1, q τ ℓ) ∧
    (∀ τ ∈ Icc p 1, envelope p q τ ≤ envelope p (movedSolution p q tl) τ) := by
  have hcm := fun τ (hτ : τ ∈ Icc p 1) => SDOSEq8.cumMass_moved_le hp0 hq tl htl htl0 hmass hτ
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- nonnegativity
    intro t ht ℓ hℓ
    unfold movedSolution
    split_ifs
    · exact SDOSEq8.envelope_nonneg hp0 hq ht
    · exact le_rfl
  · -- integrability
    intro ℓ hℓ
    have hs := htl ℓ hℓ
    have hs0 := htl0 ℓ hℓ
    refine Measure.integrableOn_of_bounded (M := 1 / tl ℓ) (measure_Icc_lt_top.ne)
      (SDOSEq8.moved_measurable p q tl ℓ).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    unfold movedSolution
    split_ifs with h
    · have ht0 : 0 < t := lt_of_lt_of_le hs0 h
      rw [Real.norm_eq_abs, abs_of_nonneg (SDOSEq8.envelope_nonneg hp0 hq ht)]
      calc envelope p q t ≤ 1 / t := SDOSEq8.envelope_le hq ht ht0
        _ ≤ 1 / tl ℓ := one_div_le_one_div_of_le hs0 h
    · simp only [norm_zero]; positivity
  · -- the constraint
    intro t ht ℓ hℓ
    have h1 := hcm t ht
    have hM := SDOSEq8.cumMass_le_one hq ht
    unfold movedSolution
    split_ifs with h
    · have ht0 : 0 < t := lt_of_lt_of_le (htl0 ℓ hℓ) h
      have : t * envelope p q t = 1 - (cumMass p q t).toReal := by
        unfold envelope; field_simp
      rw [this]
      calc ENNReal.ofReal (1 - (cumMass p q t).toReal) + cumMass p (movedSolution p q tl) t
          ≤ ENNReal.ofReal (1 - (cumMass p q t).toReal) + cumMass p q t := by gcongr
        _ = 1 := SDOSEq8.ofReal_one_sub_add hM
    · simp only [mul_zero, ENNReal.ofReal_zero, zero_add]
      exact le_trans h1 hM
  · -- mass preservation
    intro ℓ hℓ
    have hs := htl ℓ hℓ
    have hs0 := htl0 ℓ hℓ
    rw [hmass ℓ hℓ]
    have hps : p ≤ tl ℓ := hs.1
    have hs1 : tl ℓ ≤ 1 := hs.2
    have hGI : IntervalIntegrable (envelope p q) volume (tl ℓ) 1 :=
      SDOSEq8.hII hs1 (SDOSEq8.envelope_integrableOn hp0 hq hs hs0 le_rfl le_rfl)
    have hI1 : IntervalIntegrable (fun t => movedSolution p q tl t ℓ) volume p (tl ℓ) := by
      have : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume p (tl ℓ) := intervalIntegrable_const
      refine this.congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        ae_restrict_of_ae (Measure.ae_ne volume (tl ℓ))] with t htI hts
      rw [uIoc_of_le hps] at htI
      have : t < tl ℓ := lt_of_le_of_ne htI.2 hts
      simp [movedSolution, not_le.2 this]
    have hI2 : IntervalIntegrable (fun t => movedSolution p q tl t ℓ) volume (tl ℓ) 1 := by
      refine hGI.congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t htI
      rw [uIoc_of_le hs1] at htI
      simp [movedSolution, htI.1.le]
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    have hm1 : ∫ t in p..(tl ℓ), movedSolution p q tl t ℓ = 0 := by
      have : ∫ t in p..(tl ℓ), movedSolution p q tl t ℓ = ∫ t in p..(tl ℓ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae'
        · filter_upwards [Measure.ae_ne volume (tl ℓ)] with t hts htI
          have : t < tl ℓ := lt_of_le_of_ne htI.2 hts
          simp [movedSolution, not_le.2 this]
        · exact Filter.Eventually.of_forall (fun x hx =>
            absurd (lt_of_lt_of_le hx.1 (le_trans hx.2 hps)) (lt_irrefl _))
      rw [this]; simp
    have hm2 : ∫ t in (tl ℓ)..1, movedSolution p q tl t ℓ = ∫ t in (tl ℓ)..1, envelope p q t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs1] at ht
      simp [movedSolution, ht.1]
    rw [hm1, hm2, zero_add]
  · -- inequality (8)
    intro τ hτ
    unfold envelope
    have hM := SDOSEq8.cumMass_le_one hq hτ
    have hMt : cumMass p q τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hM
    have hle := ENNReal.toReal_mono hMt (hcm τ hτ)
    have hτ0 : 0 ≤ τ := le_trans hp0 hτ.1
    have : 0 ≤ 1 / τ := by positivity
    apply mul_le_mul_of_nonneg_left _ this
    linarith
