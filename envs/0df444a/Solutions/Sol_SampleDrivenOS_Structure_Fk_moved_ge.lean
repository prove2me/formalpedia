-- Prove2me | solution 1 for SampleDrivenOS.Structure.Fk_moved_ge
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:56:06.308573+00:00
-- url     : https://prove2.me/submissions/d705aa77-19fd-451f-975b-99bfe14fb1e0

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting
import Theorems.Thm_SampleDrivenOS_Structure_lemma_17

open MeasureTheory Set

namespace SDOSFk
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

/-- The core one-component comparison: moving the mass of a component to the right end,
under the ceiling `G`, does not decrease its contribution to `F_k`. -/
lemma component_le (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) (tl : ℕ → ℝ)
    {ℓ k : ℕ} (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k) (hs : tl ℓ ∈ Icc p 1) (hs0 : 0 < tl ℓ)
    (hmass : ∫ τ in p..1, q τ ℓ = ∫ τ in (tl ℓ)..1, envelope p q τ) :
    ∫ t in p..1, q t ℓ * nbTerm k ℓ t ≤
      ∫ t in p..1, movedSolution p q tl t ℓ * nbTerm k ℓ t := by
  set s := tl ℓ with hs_def
  set G := envelope p q with hG
  set w := nbTerm k ℓ with hw
  have hps : p ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hwc : Continuous w := nbTerm_continuous k ℓ
  have hwmono : MonotoneOn w (Icc 0 1) := lemma_17 k ℓ (le_trans hℓ hℓk) hℓ hℓk
  have hIcc : ∀ t ∈ Icc p 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨le_trans hp0 ht.1, ht.2⟩
  have hqint : IntegrableOn (fun t => q t ℓ) (Icc p 1) := hq.2.1 ℓ hℓ
  -- integrability facts
  have hqwint : IntegrableOn (fun t => q t ℓ * w t) (Icc p 1) := by
    have hb : ∃ C, ∀ t ∈ Icc p 1, ‖w t‖ ≤ C := by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := p) (b := 1)).exists_bound_of_continuousOn
        hwc.continuousOn
      exact ⟨C, hC⟩
    obtain ⟨C, hC⟩ := hb
    exact hqint.mul_continuousOn_of_subset hwc.continuousOn measurableSet_Icc isCompact_Icc
      subset_rfl
  have hGint : IntegrableOn G (Icc s 1) := by
    refine Measure.integrableOn_of_bounded (M := 1 / s) (measure_Icc_lt_top.ne)
      (envelope_measurable p q).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht' : t ∈ Icc p 1 := ⟨le_trans hps ht.1, ht.2⟩
    have ht0 : 0 < t := lt_of_lt_of_le hs0 ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (envelope_nonneg hp0 hq ht')]
    calc G t ≤ 1 / t := envelope_le hq ht' ht0
      _ ≤ 1 / s := one_div_le_one_div_of_le hs0 ht.1
  have hGwint : IntegrableOn (fun t => G t * w t) (Icc s 1) :=
    hGint.mul_continuousOn_of_subset hwc.continuousOn measurableSet_Icc isCompact_Icc subset_rfl
  have hII : ∀ {f : ℝ → ℝ} {a b : ℝ}, a ≤ b → IntegrableOn f (Icc a b) →
      IntervalIntegrable f volume a b := fun hab h =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 h
  have hqwI1 : IntervalIntegrable (fun t => q t ℓ * w t) volume p s :=
    hII hps (hqwint.mono_set (Icc_subset_Icc_right hs1))
  have hqwI2 : IntervalIntegrable (fun t => q t ℓ * w t) volume s 1 :=
    hII hs1 (hqwint.mono_set (Icc_subset_Icc_left hps))
  have hqI1 : IntervalIntegrable (fun t => q t ℓ) volume p s :=
    hII hps (hqint.mono_set (Icc_subset_Icc_right hs1))
  have hqI2 : IntervalIntegrable (fun t => q t ℓ) volume s 1 :=
    hII hs1 (hqint.mono_set (Icc_subset_Icc_left hps))
  have hGI : IntervalIntegrable G volume s 1 := hII hs1 hGint
  have hGwI : IntervalIntegrable (fun t => G t * w t) volume s 1 := hII hs1 hGwint
  -- the moved integral
  have hmoved : ∫ t in p..1, movedSolution p q tl t ℓ * w t = ∫ t in s..1, G t * w t := by
    have hm1 : ∫ t in p..s, movedSolution p q tl t ℓ * w t = 0 := by
      have : ∫ t in p..s, movedSolution p q tl t ℓ * w t = ∫ t in p..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae'
        · filter_upwards [Measure.ae_ne volume s] with t hts htI
          have : t < s := lt_of_le_of_ne htI.2 hts
          have h' : ¬ tl ℓ ≤ t := by rw [← hs_def]; exact not_le.2 this
          simp [movedSolution, h']
        · exact Filter.Eventually.of_forall (fun x hx =>
            absurd (lt_of_lt_of_le hx.1 (le_trans hx.2 hps)) (lt_irrefl _))
      rw [this]; simp
    have hm2 : ∫ t in s..1, movedSolution p q tl t ℓ * w t = ∫ t in s..1, G t * w t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs1] at ht
      have h' : tl ℓ ≤ t := by rw [← hs_def]; exact ht.1
      simp [movedSolution, h', hG]
    have hI1 : IntervalIntegrable (fun t => movedSolution p q tl t ℓ * w t) volume p s := by
      have : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume p s := intervalIntegrable_const
      refine this.congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        ae_restrict_of_ae (Measure.ae_ne volume s)] with t htI hts
      rw [uIoc_of_le hps] at htI
      have : t < s := lt_of_le_of_ne htI.2 hts
      have h' : ¬ tl ℓ ≤ t := by rw [← hs_def]; exact not_le.2 this
      simp [movedSolution, h']
    have hI2 : IntervalIntegrable (fun t => movedSolution p q tl t ℓ * w t) volume s 1 := by
      refine hGwI.congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t htI
      rw [uIoc_of_le hs1] at htI
      have h' : tl ℓ ≤ t := by rw [← hs_def]; exact htI.1.le
      simp [movedSolution, h', hG]
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, hm1, hm2, zero_add]
  rw [hmoved]
  -- split the original integral
  rw [← intervalIntegral.integral_add_adjacent_intervals hqwI1 hqwI2]
  have hA : ∫ t in p..s, q t ℓ * w t ≤ ∫ t in p..s, w s * q t ℓ := by
    apply intervalIntegral.integral_mono_on hps hqwI1 (hqI1.const_mul _)
    intro t ht
    have ht1 : t ∈ Icc p 1 := ⟨ht.1, le_trans ht.2 hs1⟩
    have hwts : w t ≤ w s := hwmono (hIcc t ht1) (hIcc s hs) ht.2
    have hq0 : 0 ≤ q t ℓ := hq.1 t ht1 ℓ hℓ
    nlinarith
  have hB : ∫ t in s..1, q t ℓ * w t ≤
      ∫ t in s..1, (G t * w t - w s * (G t - q t ℓ)) := by
    apply intervalIntegral.integral_mono_on hs1 hqwI2 (hGwI.sub ((hGI.sub hqI2).const_mul _))
    intro t ht
    have ht1 : t ∈ Icc p 1 := ⟨le_trans hps ht.1, ht.2⟩
    have ht0 : 0 < t := lt_of_lt_of_le hs0 ht.1
    have hwts : w s ≤ w t := hwmono (hIcc s hs) (hIcc t ht1) ht.1
    have hqG : q t ℓ ≤ G t := q_le_envelope hq ht1 ht0 hℓ
    nlinarith
  have hB' : ∫ t in s..1, (G t * w t - w s * (G t - q t ℓ)) =
      (∫ t in s..1, G t * w t) - w s * ((∫ t in s..1, G t) - ∫ t in s..1, q t ℓ) := by
    rw [intervalIntegral.integral_sub hGwI ((hGI.sub hqI2).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hGI hqI2]
  have hA' : ∫ t in p..s, w s * q t ℓ = w s * ∫ t in p..s, q t ℓ :=
    intervalIntegral.integral_const_mul _ _
  have hsplit : ∫ t in p..1, q t ℓ = (∫ t in p..s, q t ℓ) + ∫ t in s..1, q t ℓ :=
    (intervalIntegral.integral_add_adjacent_intervals hqI1 hqI2).symm
  rw [hB'] at hB
  rw [hA'] at hA
  have hm := hmass
  rw [hsplit] at hm
  have : w s * (∫ t in p..s, q t ℓ) - w s * ((∫ t in s..1, G t) - ∫ t in s..1, q t ℓ) = 0 := by
    rw [← mul_sub]
    have : (∫ t in p..s, q t ℓ) - ((∫ t in s..1, G t) - ∫ t in s..1, q t ℓ) = 0 := by
      rw [hG] at *; linarith
    rw [this, mul_zero]
  linarith

end SDOSFk

open SampleDrivenOS.Structure in
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (q : ℝ → ℕ → ℝ)
    (hq : IsFeasible p q) (tl : ℕ → ℝ) (htl : ∀ ℓ : ℕ, 1 ≤ ℓ → tl ℓ ∈ Icc p 1)
    (htl0 : ∀ ℓ : ℕ, 1 ≤ ℓ → 0 < tl ℓ)
    (hmass : ∀ ℓ : ℕ, 1 ≤ ℓ → ∫ τ in p..1, q τ ℓ = ∫ τ in (tl ℓ)..1, envelope p q τ) :
    ∀ k : ℕ, 1 ≤ k → Fk p q k ≤ Fk p (movedSolution p q tl) k := by
  intro k _
  unfold Fk
  apply Finset.sum_le_sum
  intro ℓ hℓ
  rw [Finset.mem_Icc] at hℓ
  exact SDOSFk.component_le hp0 hp1 hq tl hℓ.1 hℓ.2 (htl ℓ hℓ.1) (htl0 ℓ hℓ.1) (hmass ℓ hℓ.1)
