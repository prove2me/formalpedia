-- Prove2me | solution 1 for PrivLearn.SQSim.claim_5_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:26:43.687287+00:00
-- url     : https://prove2.me/submissions/967dd033-4734-433c-91c9-f3b9ea41f15d

import Mathlib
import Definitions.Def_PrivLearn_SQSim_Privacy
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_SQAlg
import Definitions.Def_PrivLearn_SQSim_Estimate

open PrivLearn.SQSim
open MeasureTheory

namespace Aux_Claim59

lemma eq_5_aux {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
    (R : Dom → PMF W) (hmeas : ∀ w, Measurable fun u => R u w) (u₀ : Dom) (ε β : ℝ) (t : ℕ)
    (hε : 0 < ε) (hβ : 0 < β) (ht : 1 ≤ t) (hR : IsLocalRandomizerPMF R ε)
    (w : W) (hq : 0 < R u₀ w) (v : ℝ)
    (hv : IsSQAnswer P (sqQuery (fun u => (R u w).toReal) u₀ ε) (simTolerance ε β t) v) :
    (∀ u, sqQuery (fun u => (R u w).toReal) u₀ ε u ∈ Set.Icc (-1 : ℝ) 1) ∧
    |sqEstimate (fun u => (R u w).toReal) u₀ ε v - pTarget P R w| ≤
      simPhi β t * pTarget P R w := by
  have hE1 : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
  have hEpos : 0 < Real.exp ε := Real.exp_pos ε
  have he : Real.exp (-ε) = (Real.exp ε)⁻¹ := Real.exp_neg ε
  have hr0 : 0 < (R u₀ w).toReal := ENNReal.toReal_pos hq.ne' (PMF.apply_ne_top _ _)
  have hup : ∀ u, (R u w).toReal ≤ Real.exp ε * (R u₀ w).toReal := by
    intro u
    have h := hR u u₀ w
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hEpos.le] at h2
  have hlo : ∀ u, (R u₀ w).toReal ≤ Real.exp ε * (R u w).toReal := by
    intro u
    have h := hR u₀ u w
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hEpos.le] at h2
  have hinv : (Real.exp ε)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE1
  have hinv0 : 0 < (Real.exp ε)⁻¹ := inv_pos.mpr hEpos
  have hD : 0 < Real.exp ε - Real.exp (-ε) := by rw [he]; linarith
  have hrD : 0 < (R u₀ w).toReal * (Real.exp ε - Real.exp (-ε)) := mul_pos hr0 hD
  have hEE : Real.exp ε * (Real.exp ε)⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
  have hlo' : ∀ u, (Real.exp ε)⁻¹ * (R u₀ w).toReal ≤ (R u w).toReal := by
    intro u
    have := hlo u
    rw [inv_mul_le_iff₀ hEpos]; exact this
  refine ⟨fun u => ?_, ?_⟩
  · unfold sqQuery
    constructor
    · rw [le_div_iff₀ hrD]
      have := hlo' u
      rw [he]
      nlinarith
    · rw [div_le_iff₀ hrD]
      have := hup u
      rw [he]
      nlinarith
  · have hrm : Measurable fun u => (R u w).toReal := (hmeas w).ennreal_toReal
    have hrI : Integrable (fun u => (R u w).toReal) P := by
      refine Integrable.of_bound hrm.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun u => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one (R u) w)
    have hint : ∫ u, sqQuery (fun u => (R u w).toReal) u₀ ε u ∂P
        = (pTarget P R w - (R u₀ w).toReal) / ((R u₀ w).toReal * (Real.exp ε - Real.exp (-ε))) := by
      unfold sqQuery pTarget
      rw [integral_div, integral_sub hrI (integrable_const _)]
      simp
    have hp : (Real.exp ε)⁻¹ * (R u₀ w).toReal ≤ pTarget P R w := by
      unfold pTarget
      have := integral_mono (integrable_const ((Real.exp ε)⁻¹ * (R u₀ w).toReal)) hrI hlo'
      simpa using this
    unfold IsSQAnswer at hv
    rw [hint] at hv
    have hest : sqEstimate (fun u => (R u w).toReal) u₀ ε v - pTarget P R w
        = ((R u₀ w).toReal * (Real.exp ε - Real.exp (-ε))) *
          (v - (pTarget P R w - (R u₀ w).toReal) / ((R u₀ w).toReal * (Real.exp ε - Real.exp (-ε)))) := by
      unfold sqEstimate
      field_simp
      ring
    rw [hest, abs_mul, abs_of_pos hrD]
    have h1 := mul_le_mul_of_nonneg_left hv hrD.le
    refine le_trans h1 ?_
    unfold simTolerance simPhi
    have htr : (0 : ℝ) < t := by exact_mod_cast ht
    have hE2 : Real.exp (2 * ε) = Real.exp ε * Real.exp ε := by rw [← Real.exp_add]; ring_nf
    rw [hE2, he]
    have key : (Real.exp ε - (Real.exp ε)⁻¹) / (Real.exp ε * Real.exp ε) ≤ (Real.exp ε)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc (R u₀ w).toReal * (Real.exp ε - (Real.exp ε)⁻¹) * (β / (3 * (Real.exp ε * Real.exp ε) * t))
        = (β / (3 * t)) * ((R u₀ w).toReal * ((Real.exp ε - (Real.exp ε)⁻¹) / (Real.exp ε * Real.exp ε))) := by
          field_simp
      _ ≤ (β / (3 * t)) * ((R u₀ w).toReal * (Real.exp ε)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left key hr0.le
      _ ≤ β / (3 * t) * pTarget P R w := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

lemma sqQuery_abs_le_one {Dom W : Type*} (R : Dom → PMF W) (u₀ : Dom) (ε : ℝ)
    (hε : 0 < ε) (hR : IsLocalRandomizerPMF R ε) (w : W) (hq : 0 < R u₀ w) (u : Dom) :
    |sqQuery (fun u => (R u w).toReal) u₀ ε u| ≤ 1 := by
  have hE1 : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
  have hEpos : 0 < Real.exp ε := Real.exp_pos ε
  have he : Real.exp (-ε) = (Real.exp ε)⁻¹ := Real.exp_neg ε
  have hr0 : 0 < (R u₀ w).toReal := ENNReal.toReal_pos hq.ne' (PMF.apply_ne_top _ _)
  have hup : (R u w).toReal ≤ Real.exp ε * (R u₀ w).toReal := by
    have h := hR u u₀ w
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hEpos.le] at h2
  have hlo : (R u₀ w).toReal ≤ Real.exp ε * (R u w).toReal := by
    have h := hR u₀ u w
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hEpos.le] at h2
  have hinv : (Real.exp ε)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE1
  have hD : 0 < Real.exp ε - Real.exp (-ε) := by rw [he]; linarith
  have hrD : 0 < (R u₀ w).toReal * (Real.exp ε - Real.exp (-ε)) := mul_pos hr0 hD
  have hEE : Real.exp ε * (Real.exp ε)⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
  have hlo' : (Real.exp ε)⁻¹ * (R u₀ w).toReal ≤ (R u w).toReal := by
    rw [inv_mul_le_iff₀ hEpos]; exact hlo
  rw [abs_le]
  unfold sqQuery
  constructor
  · rw [le_div_iff₀ hrD, he]; nlinarith
  · rw [div_le_iff₀ hrD, he]; nlinarith

lemma loc_real {Dom W : Type*} (R : Dom → PMF W) (e : ℝ) (h : IsLocalRandomizerPMF R e)
    (u u' : Dom) (w : W) : (R u w).toReal ≤ Real.exp e * (R u' w).toReal := by
  have h1 := h u u' w
  have hne : ENNReal.ofReal (Real.exp e) * R u' w ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)
  have := ENNReal.toReal_mono hne h1
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos e).le] at this

lemma ratio (x₁ x₂ p₁ p₂ t : ℝ) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 3)
    (h₁ : |x₁ - p₁| ≤ t * p₁) (h₂ : |x₂ - p₂| ≤ t * p₂) :
    |x₁ / x₂ - p₁ / p₂| ≤ 3 * t * (p₁ / p₂) := by
  obtain ⟨a1, a2⟩ := abs_le.mp h₁
  obtain ⟨b1, b2⟩ := abs_le.mp h₂
  have hx₂ : 0 < x₂ := by nlinarith
  rw [abs_le]
  have key1 : x₁ / x₂ ≤ (1 + 3 * t) * (p₁ / p₂) := by
    rw [div_le_iff₀ hx₂]
    have : (1 + 3 * t) * (p₁ / p₂) * x₂ ≥ (1 + 3 * t) * (p₁ / p₂) * ((1 - t) * p₂) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : (1 + 3 * t) * (p₁ / p₂) * ((1 - t) * p₂) = (1 + 3 * t) * (1 - t) * p₁ := by
      field_simp
    nlinarith
  have key2 : (1 - 3 * t) * (p₁ / p₂) ≤ x₁ / x₂ := by
    rw [le_div_iff₀ hx₂]
    by_cases hneg : 1 - 3 * t ≤ 0
    · have : (1 - 3 * t) * (p₁ / p₂) * x₂ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)) hx₂.le
      nlinarith
    · rw [not_le] at hneg
      have : (1 - 3 * t) * (p₁ / p₂) * x₂ ≤ (1 - 3 * t) * (p₁ / p₂) * ((1 + t) * p₂) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e2 : (1 - 3 * t) * (p₁ / p₂) * ((1 + t) * p₂) = (1 - 3 * t) * (1 + t) * p₁ := by
        field_simp
      nlinarith
  constructor <;> nlinarith [div_pos hp₁ hp₂]

lemma lintegral_pmf_tsum {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (R : Dom → PMF W) (hmeas : ∀ w, Measurable fun u => R u w)
    (u₀ : Dom) (ε : ℝ) (hR : IsLocalRandomizerPMF R ε) :
    ∑' w, (∫⁻ u, R u w ∂P) = 1 := by
  set S : Set W := (R u₀).support with hS
  have hSc : S.Countable := (R u₀).support_countable
  have : Countable S := hSc.to_subtype
  have hzero : ∀ u w, w ∉ S → R u w = 0 := by
    intro u w hw
    have h1 := hR u u₀ w
    have h2 : R u₀ w = 0 := by simpa [hS, PMF.mem_support_iff] using hw
    rw [h2, mul_zero] at h1
    exact le_antisymm h1 bot_le
  have hsupp : Function.support (fun w => ∫⁻ u, R u w ∂P) ⊆ S := by
    intro w hw
    by_contra hwS
    apply hw
    simp only
    rw [lintegral_congr (fun u => hzero u w hwS), lintegral_zero]
  rw [← tsum_subtype_eq_of_support_subset hsupp,
    ← lintegral_tsum (fun w : S => (hmeas w.1).aemeasurable)]
  have hone : ∀ u, ∑' w : S, R u w = 1 := by
    intro u
    have hsu : Function.support (fun w => R u w) ⊆ S := by
      intro w hw
      by_contra hwS
      exact hw (hzero u w hwS)
    rw [tsum_subtype_eq_of_support_subset hsu]
    exact PMF.tsum_coe (R u)
  simp only [hone, lintegral_const, measure_univ, mul_one]

lemma ofReal_pTarget_eq_lintegral {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (R : Dom → PMF W) (hmeas : ∀ w, Measurable fun u => R u w) (w : W) :
    ENNReal.ofReal (pTarget P R w) = ∫⁻ u, R u w ∂P := by
  have hfin : (∫⁻ u, R u w ∂P) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
    calc (∫⁻ u, R u w ∂P) ≤ ∫⁻ _, (1 : ENNReal) ∂P := lintegral_mono fun u => PMF.coe_le_one (R u) w
      _ = 1 := by simp
  have hpL : pTarget P R w = (∫⁻ u, R u w ∂P).toReal := by
    unfold pTarget
    exact integral_toReal (hmeas w).aemeasurable
      (Filter.Eventually.of_forall (fun u => lt_of_le_of_lt (PMF.coe_le_one _ _) ENNReal.one_lt_top))
  rw [hpL, ENNReal.ofReal_toReal hfin]

lemma iteration_analysis_aux {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (R : Dom → PMF W) (hmeas : ∀ w, Measurable fun u => R u w)
    (u₀ : Dom) (ε β : ℝ) (t : ℕ) (_hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t)
    (hR : IsLocalRandomizerPMF R ε) (pt : W → ℝ)
    (hpt : ∀ w, 0 < R u₀ w → |pt w - pTarget P R w| ≤ simPhi β t * pTarget P R w) :
    let φ : ℝ := simPhi β t
    let acc : W → ℝ := fun w => pt w / ((R u₀ w).toReal * (1 + φ) * Real.exp ε)
    let pTerm : ℝ := ∑' w, (R u₀ w).toReal * acc w
    (∀ w, 0 < R u₀ w → 0 ≤ acc w ∧ acc w ≤ 1) ∧
    Summable (fun w => (R u₀ w).toReal * acc w) ∧
    (1 - φ) / (1 + φ) * Real.exp (-ε) ≤ pTerm ∧ pTerm ≤ Real.exp (-ε) ∧
    ∀ w, |(R u₀ w).toReal * acc w / pTerm - pTarget P R w| ≤ 3 * φ * pTarget P R w := by
  intro φ acc pTerm
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hφ0 : 0 < φ := by
    show 0 < simPhi β t
    unfold simPhi
    positivity
  have hφ3 : φ ≤ 1 / 3 := by
    show simPhi β t ≤ 1 / 3
    unfold simPhi
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set q : W → ℝ := fun w => (R u₀ w).toReal with hq
  set p : W → ℝ := fun w => pTarget P R w with hp
  have hq0 : ∀ w, 0 ≤ q w := fun w => ENNReal.toReal_nonneg
  have hint : ∀ w, Integrable (fun u => (R u w).toReal) P := by
    intro w
    refine Integrable.of_bound (hmeas w).ennreal_toReal.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun u => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one (R u) w)
  have hp_hi : ∀ w, p w ≤ Real.exp ε * q w := by
    intro w
    have := integral_mono (hint w) (integrable_const (Real.exp ε * q w))
      (fun u => loc_real R ε hR u u₀ w)
    simpa [hp, pTarget] using this
  have hp0 : ∀ w, 0 ≤ p w := fun w => integral_nonneg (fun u => ENNReal.toReal_nonneg)
  have hL : ∑' w, (∫⁻ u, R u w ∂P) = 1 := lintegral_pmf_tsum P R hmeas u₀ ε hR
  have hpL : ∀ w, p w = (∫⁻ u, R u w ∂P).toReal := by
    intro w
    simp only [hp, pTarget]
    exact integral_toReal (hmeas w).aemeasurable
      (Filter.Eventually.of_forall (fun u => lt_of_le_of_lt (PMF.coe_le_one _ _) ENNReal.one_lt_top))
  have hfin : ∀ w, (∫⁻ u, R u w ∂P) ≠ ⊤ := by
    intro w
    refine ne_of_lt (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
    rw [← hL]
    exact ENNReal.le_tsum w
  have hpsum : Summable p := by
    have := ENNReal.summable_toReal (f := fun w => ∫⁻ u, R u w ∂P) (by rw [hL]; exact ENNReal.one_ne_top)
    exact this.congr (fun w => (hpL w).symm)
  have hp1 : ∑' w, p w = 1 := by
    rw [tsum_congr hpL, ← ENNReal.tsum_toReal_eq hfin, hL, ENNReal.toReal_one]
  set K := (1 + φ) * Real.exp ε with hK
  have hKpos : 0 < K := by positivity
  have hc : ∀ w, q w * acc w = if 0 < R u₀ w then pt w / K else 0 := by
    intro w
    split_ifs with h
    · have hqw : 0 < q w := ENNReal.toReal_pos h.ne' (PMF.apply_ne_top _ _)
      have hq' : ((R u₀) w).toReal ≠ 0 := hqw.ne'
      simp only [acc, hq, hK]
      field_simp
    · have : R u₀ w = 0 := le_antisymm (not_lt.mp h) bot_le
      simp only [acc, hq, this, ENNReal.toReal_zero, zero_mul]
  have hcb : ∀ w, (1 - φ) * p w / K ≤ q w * acc w ∧ q w * acc w ≤ (1 + φ) * p w / K := by
    intro w
    rw [hc w]
    split_ifs with h
    · obtain ⟨a1, a2⟩ := abs_le.mp (hpt w h)
      constructor
      · apply div_le_div_of_nonneg_right _ hKpos.le; linarith
      · apply div_le_div_of_nonneg_right _ hKpos.le; linarith
    · have : R u₀ w = 0 := le_antisymm (not_lt.mp h) bot_le
      have hq0' : q w = 0 := by simp [hq, this]
      have : p w = 0 := le_antisymm (by have := hp_hi w; rw [hq0', mul_zero] at this; exact this)
        (hp0 w)
      rw [this]; simp
  have hcsum : Summable (fun w => q w * acc w) := by
    refine Summable.of_nonneg_of_le (fun w => ?_) (fun w => ?_) (hpsum.mul_left ((1 + φ) / K))
    · exact le_trans (div_nonneg (mul_nonneg (by linarith) (hp0 w)) hKpos.le) (hcb w).1
    · have := (hcb w).2; rw [mul_div_right_comm] at this; linarith [this]
  have hlo' : ∀ w, (1 - φ) / K * p w ≤ q w * acc w := by
    intro w
    calc (1 - φ) / K * p w = (1 - φ) * p w / K := by ring
      _ ≤ q w * acc w := (hcb w).1
  have hhi' : ∀ w, q w * acc w ≤ (1 + φ) / K * p w := by
    intro w
    calc q w * acc w ≤ (1 + φ) * p w / K := (hcb w).2
      _ = (1 + φ) / K * p w := by ring
  have hTlo : (1 - φ) / K ≤ pTerm := by
    have h1 : ∑' w, (1 - φ) / K * p w ≤ ∑' w, q w * acc w :=
      Summable.tsum_le_tsum hlo' (hpsum.mul_left ((1 - φ) / K)) hcsum
    rw [tsum_mul_left, hp1, mul_one] at h1
    exact h1
  have hThi : pTerm ≤ (1 + φ) / K := by
    have h1 : ∑' w, q w * acc w ≤ ∑' w, (1 + φ) / K * p w :=
      Summable.tsum_le_tsum hhi' hcsum (hpsum.mul_left ((1 + φ) / K))
    rw [tsum_mul_left, hp1, mul_one] at h1
    exact h1
  have hKe : (1 + φ) / K = Real.exp (-ε) := by
    rw [hK, Real.exp_neg]; field_simp
  refine ⟨fun w hw => ?_, hcsum, ?_, ?_, fun w => ?_⟩
  · have hqw : 0 < q w := ENNReal.toReal_pos hw.ne' (PMF.apply_ne_top _ _)
    obtain ⟨a1, a2⟩ := abs_le.mp (hpt w hw)
    have hden : 0 < q w * (1 + φ) * Real.exp ε := by positivity
    constructor
    · apply div_nonneg _ hden.le
      nlinarith [hp0 w]
    · rw [div_le_one hden]
      have := hp_hi w
      nlinarith
  · calc (1 - φ) / (1 + φ) * Real.exp (-ε) = (1 - φ) / K := by
          rw [← hKe]; field_simp
      _ ≤ pTerm := hTlo
  · rw [← hKe]; exact hThi
  · by_cases hpw : p w = 0
    · have h1 := (hcb w).2
      have h2 := (hcb w).1
      rw [hpw] at h1 h2
      simp only [mul_zero, zero_div] at h1 h2
      have : q w * acc w = 0 := le_antisymm h1 h2
      show |q w * acc w / pTerm - p w| ≤ 3 * φ * p w
      rw [this, hpw]; simp
    · have hppos : 0 < p w := lt_of_le_of_ne (hp0 w) (Ne.symm hpw)
      have hx₁ : |q w * acc w * K - p w| ≤ φ * p w := by
        obtain ⟨b1, b2⟩ := hcb w
        rw [div_le_iff₀ hKpos] at b1
        rw [le_div_iff₀ hKpos] at b2
        rw [abs_le]; constructor <;> nlinarith
      have hx₂ : |pTerm * K - 1| ≤ φ * 1 := by
        rw [div_le_iff₀ hKpos] at hTlo
        rw [le_div_iff₀ hKpos] at hThi
        rw [abs_le]; constructor <;> nlinarith
      have := ratio (q w * acc w * K) (pTerm * K) (p w) 1 φ hppos one_pos hφ0.le hφ3
        hx₁ hx₂
      rw [div_one] at this
      have e : q w * acc w * K / (pTerm * K) = q w * acc w / pTerm := by
        rw [mul_div_mul_right _ _ hKpos.ne']
      rw [e] at this
      exact this

/-! ### Part 1: Product PMF and Leader-Grouped Randomizers -/

noncomputable def pmfPi {W : Type*} : ∀ {m : ℕ}, (Fin m → PMF W) → PMF (Fin m → W)
  | 0, _ => PMF.pure Fin.elim0
  | m + 1, Q => (Q 0).bind fun w0 => (pmfPi (fun j : Fin m => Q j.succ)).map (Fin.cons w0)

lemma fin_eq_cons_iff {W : Type*} {m : ℕ} (v : Fin (m + 1) → W) (w0 : W) (vr : Fin m → W) :
    v = Fin.cons w0 vr ↔ w0 = v 0 ∧ vr = Fin.tail v := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact (Fin.cons_self_tail v).symm

lemma pmfPi_apply {W : Type*} :
    ∀ {m : ℕ} (Q : Fin m → PMF W) (v : Fin m → W),
      pmfPi Q v = ∏ j : Fin m, Q j (v j)
  | 0, Q, v => by
    have hv : v = Fin.elim0 := Subsingleton.elim v Fin.elim0
    simp [pmfPi, hv]
  | m + 1, Q, v => by
    classical
    simp only [pmfPi, PMF.bind_apply, PMF.map_apply, fin_eq_cons_iff]
    have h_inner : ∀ w0 : W,
        (∑' vr : Fin m → W, if w0 = v 0 ∧ vr = Fin.tail v then pmfPi (fun j => Q j.succ) vr else 0) =
          if w0 = v 0 then pmfPi (fun j => Q j.succ) (Fin.tail v) else 0 := by
      intro w0
      by_cases hw0 : w0 = v 0
      · simp only [hw0, true_and, ite_true, tsum_ite_eq]
      · simp only [hw0, false_and, ite_false, tsum_zero]
    simp_rw [h_inner, mul_ite, mul_zero, tsum_ite_eq]
    rw [pmfPi_apply (fun j => Q j.succ) (Fin.tail v), Fin.prod_univ_succ]
    rfl

lemma lintegral_pi_prod_fn {Dom : Type*} [MeasurableSpace Dom] (μ : Measure Dom)
    [IsProbabilityMeasure μ] :
    ∀ {n : ℕ} (g : Fin n → Dom → ENNReal), (∀ i, Measurable (g i)) →
      (∫⁻ z : Fin n → Dom, (∏ i : Fin n, g i (z i)) ∂(Measure.pi fun _ : Fin n => μ)) =
        ∏ i : Fin n, ∫⁻ x : Dom, g i x ∂μ
  | 0, _, _ => by simp
  | m + 1, g, hg => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Dom) 0
    have hmp : (μ.prod (Measure.pi fun _ : Fin m => μ)).map e.symm =
        Measure.pi (fun _ : Fin (m + 1) => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm.map_eq
    have hm_prod : Measurable (fun z : Fin (m + 1) → Dom => ∏ i : Fin (m + 1), g i (z i)) :=
      Finset.measurable_prod Finset.univ fun i _ => (hg i).comp (measurable_pi_apply i)
    rw [← hmp, lintegral_map hm_prod e.symm.measurable]
    have h_split : (fun p : Dom × (Fin m → Dom) => ∏ i : Fin (m + 1), g i (e.symm p i)) =
        fun p : Dom × (Fin m → Dom) => g 0 p.1 * ∏ j : Fin m, g j.succ (p.2 j) := by
      ext ⟨x, y⟩
      have he : e.symm (x, y) = (0 : Fin (m + 1)).insertNth x y := rfl
      rw [he, Fin.prod_univ_succAbove _ 0, Fin.insertNth_apply_same]
      simp
    rw [h_split]
    have hm_prod_m : Measurable (fun y : Fin m → Dom => ∏ j : Fin m, g j.succ (y j)) :=
      Finset.measurable_prod Finset.univ fun j _ => (hg j.succ).comp (measurable_pi_apply j)
    rw [lintegral_prod_mul (hg 0).aemeasurable hm_prod_m.aemeasurable,
      lintegral_pi_prod_fn μ (fun j => g j.succ) (fun j => hg j.succ), Fin.prod_univ_succ]

lemma lintegral_prod_subsingleton {Dom α : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (F : Finset α) (hF : (F : Set α).Subsingleton)
    (f : α → Dom → ENNReal) :
    (∫⁻ u, (∏ k ∈ F, f k u) ∂P) = ∏ k ∈ F, ∫⁻ u, f k u ∂P := by
  rcases Finset.eq_empty_or_nonempty F with rfl | ⟨k₀, hk₀⟩
  · simp
  · have h_eq : F = {k₀} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hk₀, fun k hk => hF hk hk₀⟩
    subst h_eq
    simp

/-! ### Part 2: State Machine and Finite-Horizon Simulation of `t` Independent Randomizers -/

noncomputable def bernoulliPMF (p : ℝ) : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (min 1 (max 0 p)) else ENNReal.ofReal (1 - min 1 (max 0 p)))
    (by
      rw [Fintype.sum_bool]
      have h0 : 0 ≤ min 1 (max 0 p) := le_min zero_le_one (le_max_left 0 p)
      have h1 : 0 ≤ 1 - min 1 (max 0 p) := sub_nonneg.mpr (min_le_left 1 (max 0 p))
      simp only [ite_true, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_add h0 h1, add_sub_cancel, ENNReal.ofReal_one])

noncomputable def mixPMF {α : Type*} (p : ℝ) (P_acc P_rej : PMF α) : PMF α :=
  (bernoulliPMF p).bind (fun b => if b then P_acc else P_rej)

lemma mixPMF_apply_of_mem_Icc {α : Type*} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P_acc P_rej : PMF α) (x : α) :
    mixPMF p P_acc P_rej x =
      ENNReal.ofReal p * P_acc x + ENNReal.ofReal (1 - p) * P_rej x := by
  simp [mixPMF, bernoulliPMF, PMF.bind_apply, tsum_fintype, max_eq_right hp0, min_eq_right hp1]

inductive SimState (Out V : Type) (t : ℕ)
  | active (k : ℕ) (b : Fin t → V) (v : V)
  | done (o : Out)

noncomputable def initStage {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (k : ℕ) (b : Fin t → V) : PMF (SimState Out V t) :=
  if hk : k < t then
    (M ⟨k, hk⟩ u₀).map (fun v => SimState.active k b v)
  else
    PMF.pure (SimState.done (outV b))

noncomputable def simAccProb {Dom V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (M : Fin t → Dom → PMF V) (k : Fin t) (v : V) (ans : ℝ) : ℝ :=
  sqEstimate (fun u => (M k u v).toReal) u₀ ε ans /
    ((M k u₀ v).toReal * (1 + simPhi β t) * Real.exp ε)

noncomputable def simAlg {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out) :
    SQAlg Dom Out (SimState Out V t) where
  start := initStage u₀ M outV 0 (fun _ => v₀)
  step s :=
    match s with
    | .done o => .inl o
    | .active k b v =>
      if hk : k < t then
        if _hq : 0 < M ⟨k, hk⟩ u₀ v then
          let g : Dom → ℝ := sqQuery (fun u => (M ⟨k, hk⟩ u v).toReal) u₀ ε
          let τ : ℝ := simTolerance ε β t
          let nextKernel : ℝ → PMF (SimState Out V t) := fun ans =>
            mixPMF (simAccProb u₀ ε β M ⟨k, hk⟩ v ans)
              (initStage u₀ M outV (k + 1) (Function.update b ⟨k, hk⟩ v))
              (initStage u₀ M outV k b)
          .inr (g, τ, nextKernel)
        else
          .inl (outV b)
      else
        .inl (outV b)

lemma simAlg_asksOnly {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (hε : 0 < ε) (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε) :
    (simAlg u₀ ε β v₀ M outV).AsksOnly (simTolerance ε β t) := by
  intro s g τ' k_next hs
  cases s with
  | done o =>
    simp [simAlg] at hs
  | active k b v =>
    dsimp [simAlg] at hs
    split_ifs at hs with hk hq
    cases hs
    refine ⟨rfl, ?_, fun u => sqQuery_abs_le_one (M ⟨k, hk⟩) u₀ ε hε (hM_loc ⟨k, hk⟩) v hq u⟩
    unfold sqQuery
    exact (((hM_meas ⟨k, hk⟩ v).ennreal_toReal.sub measurable_const).div_const _)

noncomputable def stepsFrom {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ) :
    ℕ → (Out ⊕ List σ) → PMF (Out ⊕ List σ)
  | 0, x => PMF.pure x
  | N + 1, x => (B.next O x).bind (stepsFrom B O N)

lemma stepsFrom_bind_next {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ) :
    ∀ (N : ℕ) (x : Out ⊕ List σ),
      (stepsFrom B O N x).bind (B.next O) = stepsFrom B O (N + 1) x
  | 0, x => by simp [stepsFrom]
  | N + 1, x => by
    rw [stepsFrom, PMF.bind_bind]
    congr 1
    funext y
    exact stepsFrom_bind_next B O N y

lemma run_eq_stepsFrom {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ) :
    ∀ N : ℕ, B.run O N = stepsFrom B O N (.inr [])
  | 0 => rfl
  | N + 1 => by
    rw [SQAlg.run, run_eq_stepsFrom B O N, stepsFrom_bind_next]

lemma stepsFrom_inl {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ) :
    ∀ (N : ℕ) (o : Out), stepsFrom B O N (.inl o) = PMF.pure (.inl o)
  | 0, _ => rfl
  | N + 1, o => by simp [stepsFrom, SQAlg.next, stepsFrom_inl B O N o]

noncomputable def stageLaw {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (k : ℕ) (b : Fin t → V) (h : List (SimState Out V t)) :
    PMF (Out ⊕ List (SimState Out V t)) :=
  (initStage u₀ M outV k b).map (fun s => .inr (s :: h))

noncomputable def stageRun {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    (N : ℕ) (k : ℕ) (b : Fin t → V) (h : List (SimState Out V t)) :
    PMF (Out ⊕ List (SimState Out V t)) :=
  (stageLaw u₀ M outV k b h).bind (stepsFrom (simAlg u₀ ε β v₀ M outV) O N)

lemma run_succ_eq_stageRun {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ) (N : ℕ) :
    (simAlg u₀ ε β v₀ M outV).run O (N + 1) =
      stageRun u₀ ε β v₀ M outV O N 0 (fun _ => v₀) [] := by
  rw [run_eq_stepsFrom]
  rfl

lemma stageRun_zero {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    (k : ℕ) (b : Fin t → V) (h : List (SimState Out V t)) :
    stageRun u₀ ε β v₀ M outV O 0 k b h = stageLaw u₀ M outV k b h := by
  simp [stageRun, stepsFrom]

lemma stageRun_succ {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    (N : ℕ) (k : ℕ) (b : Fin t → V) (h : List (SimState Out V t)) :
    stageRun u₀ ε β v₀ M outV O (N + 1) k b h =
      ((stageLaw u₀ M outV k b h).bind ((simAlg u₀ ε β v₀ M outV).next O)).bind
        (stepsFrom (simAlg u₀ ε β v₀ M outV) O N) := by
  simp [stageRun, stepsFrom, PMF.bind_bind]

lemma stageLaw_bind_next_of_ge {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    {k : ℕ} (hk : ¬ k < t) (b : Fin t → V) (h : List (SimState Out V t)) :
    (stageLaw u₀ M outV k b h).bind ((simAlg u₀ ε β v₀ M outV).next O) =
      PMF.pure (.inl (outV b)) := by
  simp [stageLaw, initStage, hk, SQAlg.next, simAlg]

lemma stageRun_succ_of_ge {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    (N : ℕ) {k : ℕ} (hk : ¬ k < t) (b : Fin t → V) (h : List (SimState Out V t)) :
    stageRun u₀ ε β v₀ M outV O (N + 1) k b h = PMF.pure (.inl (outV b)) := by
  rw [stageRun_succ, stageLaw_bind_next_of_ge u₀ ε β v₀ M outV O hk,
    PMF.pure_bind, stepsFrom_inl]

lemma map_mixPMF_apply {α β : Type*} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q : PMF α) (f : α → β) (y : β) :
    (mixPMF p P Q).map f y =
      ENNReal.ofReal p * P.map f y + ENNReal.ofReal (1 - p) * Q.map f y := by
  classical
  simp only [PMF.map_apply, mixPMF_apply_of_mem_Icc p hp0 hp1]
  have h1 : ∀ a : α,
      (if y = f a then ENNReal.ofReal p * P a + ENNReal.ofReal (1 - p) * Q a else 0) =
        ENNReal.ofReal p * (if y = f a then P a else 0) +
        ENNReal.ofReal (1 - p) * (if y = f a then Q a else 0) := by
    intro a; split_ifs <;> simp
  simp_rw [h1]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

lemma bind_on_linear {α β : Type*} (D D₁ D₂ : PMF α) (K : α → PMF β) (a₁ a₂ : ENNReal)
    (hD : ∀ x, D x = a₁ * D₁ x + a₂ * D₂ x) (c : β) :
    D.bind K c = a₁ * D₁.bind K c + a₂ * D₂.bind K c := by
  simp only [PMF.bind_apply, hD, add_mul, mul_assoc]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

lemma stageRun_succ_apply_of_lt {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    (N : ℕ) {k : ℕ} (hk : k < t) (b : Fin t → V) (h : List (SimState Out V t))
    (hacc : ∀ v, 0 < M ⟨k, hk⟩ u₀ v →
      0 ≤ simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h)) ∧
      simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h)) ≤ 1)
    (c : Out ⊕ List (SimState Out V t)) :
    stageRun u₀ ε β v₀ M outV O (N + 1) k b h c =
      ∑' v : V,
        (M ⟨k, hk⟩ u₀ v *
          ENNReal.ofReal (simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
            (.active k b v :: h) c +
         M ⟨k, hk⟩ u₀ v *
          ENNReal.ofReal (1 - simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h) c) := by
  classical
  set B := simAlg u₀ ε β v₀ M outV
  have hL : stageLaw u₀ M outV k b h =
      (M ⟨k, hk⟩ u₀).map (fun v => .inr (.active k b v :: h)) := by
    simp [stageLaw, initStage, hk, PMF.map_comp, Function.comp_def]
  rw [stageRun_succ, hL, PMF.bind_map, PMF.bind_bind, PMF.bind_apply]
  simp only [Function.comp_def]
  refine tsum_congr fun v => ?_
  by_cases hq : 0 < M ⟨k, hk⟩ u₀ v
  · obtain ⟨ha0, ha1⟩ := hacc v hq
    have hnext : B.next O (.inr (.active k b v :: h)) =
        (mixPMF (simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h)))
          (initStage u₀ M outV (k + 1) (Function.update b ⟨k, hk⟩ v))
          (initStage u₀ M outV k b)).map (fun s' => .inr (s' :: .active k b v :: h)) := by
      simp [B, SQAlg.next, simAlg, hk, hq]
    have hbind : ((B.next O (.inr (.active k b v :: h))).bind (stepsFrom B O N)) c =
        ENNReal.ofReal (simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
            (.active k b v :: h) c +
        ENNReal.ofReal (1 - simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h) c := by
      rw [hnext]
      exact bind_on_linear _
        (stageLaw u₀ M outV (k + 1) (Function.update b ⟨k, hk⟩ v) (.active k b v :: h))
        (stageLaw u₀ M outV k b (.active k b v :: h))
        (stepsFrom B O N) _ _
        (map_mixPMF_apply _ ha0 ha1 _ _ _) c
    rw [hbind, mul_add, ← mul_assoc, ← mul_assoc]
  · have hzero : M ⟨k, hk⟩ u₀ v = 0 := le_antisymm (not_lt.mp hq) bot_le
    simp [hzero]

/-! ### Part 3: Expected Query Bound -/

noncomputable def qMass {Dom Out σ : Type} (B : SQAlg Dom Out σ) (D : PMF (Out ⊕ List σ)) : ENNReal :=
  D.toOuterMeasure {c | B.Querying c}

lemma qMass_le_one {Dom Out σ : Type} (B : SQAlg Dom Out σ) (D : PMF (Out ⊕ List σ)) :
    qMass B D ≤ 1 := by
  unfold qMass
  calc D.toOuterMeasure {c | B.Querying c}
      ≤ D.toOuterMeasure Set.univ := D.toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := by simp [PMF.toOuterMeasure_apply, PMF.tsum_coe]

lemma qMass_stageRun_zero_of_ge {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    {k : ℕ} (hk : ¬ k < t) (b : Fin t → V) (h : List (SimState Out V t)) :
    qMass (simAlg u₀ ε β v₀ M outV) (stageRun u₀ ε β v₀ M outV O 0 k b h) = 0 := by
  rw [stageRun_zero]
  simp [qMass, stageLaw, initStage, hk, PMF.toOuterMeasure_pure_apply, SQAlg.Querying, simAlg]

lemma qMass_pure_inl {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out) (o : Out) :
    qMass (simAlg u₀ ε β v₀ M outV) (PMF.pure (.inl o)) = 0 := by
  simp [qMass, PMF.toOuterMeasure_pure_apply, SQAlg.Querying]

lemma qMass_stageRun_succ_of_lt {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    (N : ℕ) {k : ℕ} (hk : k < t) (b : Fin t → V) (h : List (SimState Out V t))
    (hacc : ∀ v, 0 < M ⟨k, hk⟩ u₀ v →
      0 ≤ simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h)) ∧
      simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h)) ≤ 1) :
    qMass (simAlg u₀ ε β v₀ M outV) (stageRun u₀ ε β v₀ M outV O (N + 1) k b h) =
      ∑' v : V,
        (M ⟨k, hk⟩ u₀ v *
          ENNReal.ofReal (simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          qMass (simAlg u₀ ε β v₀ M outV)
            (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
              (.active k b v :: h)) +
         M ⟨k, hk⟩ u₀ v *
          ENNReal.ofReal (1 - simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          qMass (simAlg u₀ ε β v₀ M outV)
            (stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h))) := by
  classical
  set B := simAlg u₀ ε β v₀ M outV
  unfold qMass
  simp only [PMF.toOuterMeasure_apply]
  have h_ind : ∀ c : Out ⊕ List (SimState Out V t),
      {c | B.Querying c}.indicator (stageRun u₀ ε β v₀ M outV O (N + 1) k b h) c =
      ∑' v : V,
        (M ⟨k, hk⟩ u₀ v *
          ENNReal.ofReal (simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          {c | B.Querying c}.indicator
            (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
              (.active k b v :: h)) c +
         M ⟨k, hk⟩ u₀ v *
          ENNReal.ofReal (1 - simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          {c | B.Querying c}.indicator
            (stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h)) c) := by
    intro c
    by_cases hc : c ∈ {c | B.Querying c}
    · simp only [Set.indicator_of_mem hc,
        stageRun_succ_apply_of_lt u₀ ε β v₀ M outV O N hk b h hacc c]
    · simp only [Set.indicator_of_notMem hc, mul_zero, add_zero, tsum_zero]
  simp_rw [h_ind]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun v => ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

lemma step_weights_sum {W : Type*} (R : PMF W) (acc : W → ℝ)
    (hacc : ∀ w, 0 < R w → 0 ≤ acc w ∧ acc w ≤ 1)
    (hsum : Summable (fun w => (R w).toReal * acc w)) :
    (∑' w, R w * ENNReal.ofReal (acc w) = ENNReal.ofReal (∑' w, (R w).toReal * acc w)) ∧
    (∑' w, R w * ENNReal.ofReal (1 - acc w) = ENNReal.ofReal (1 - ∑' w, (R w).toReal * acc w)) ∧
    0 ≤ (∑' w, (R w).toReal * acc w) ∧ (∑' w, (R w).toReal * acc w) ≤ 1 := by
  set pTerm := ∑' w, (R w).toReal * acc w
  have hterm_eq : ∀ w, R w * ENNReal.ofReal (acc w) = ENNReal.ofReal ((R w).toReal * acc w) := by
    intro w
    by_cases hw : 0 < R w
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top R w)]
    · have hz : R w = 0 := le_antisymm (not_lt.mp hw) bot_le
      simp [hz]
  have hterm_nonneg : ∀ w, 0 ≤ (R w).toReal * acc w := by
    intro w
    by_cases hw : 0 < R w
    · exact mul_nonneg ENNReal.toReal_nonneg (hacc w hw).1
    · have hz : R w = 0 := le_antisymm (not_lt.mp hw) bot_le
      simp [hz]
  have hp0 : 0 ≤ pTerm := tsum_nonneg hterm_nonneg
  have h1 : ∑' w, R w * ENNReal.ofReal (acc w) = ENNReal.ofReal pTerm := by
    simp_rw [hterm_eq]
    exact (ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hsum).symm
  have h_add : (∑' w, R w * ENNReal.ofReal (acc w)) + (∑' w, R w * ENNReal.ofReal (1 - acc w)) = 1 := by
    rw [← ENNReal.tsum_add]
    have hpt : ∀ w, R w * ENNReal.ofReal (acc w) + R w * ENNReal.ofReal (1 - acc w) = R w := by
      intro w
      by_cases hw : 0 < R w
      · obtain ⟨ha0, ha1⟩ := hacc w hw
        rw [← mul_add, ← ENNReal.ofReal_add ha0 (sub_nonneg.mpr ha1), add_sub_cancel,
          ENNReal.ofReal_one, mul_one]
      · have hz : R w = 0 := le_antisymm (not_lt.mp hw) bot_le
        simp [hz]
    simp_rw [hpt]
    exact PMF.tsum_coe R
  have hp1 : pTerm ≤ 1 := by
    have hle : ENNReal.ofReal pTerm ≤ 1 := by
      rw [← h1, ← h_add]
      exact le_self_add
    exact ENNReal.ofReal_le_one.mp hle
  have h2 : ∑' w, R w * ENNReal.ofReal (1 - acc w) = ENNReal.ofReal (1 - pTerm) := by
    have h_eq : (∑' w, R w * ENNReal.ofReal (1 - acc w)) + ENNReal.ofReal pTerm =
        ENNReal.ofReal (1 - pTerm) + ENNReal.ofReal pTerm := by
      calc (∑' w, R w * ENNReal.ofReal (1 - acc w)) + ENNReal.ofReal pTerm
          = ENNReal.ofReal pTerm + ∑' w, R w * ENNReal.ofReal (1 - acc w) := add_comm _ _
        _ = (∑' w, R w * ENNReal.ofReal (acc w)) + ∑' w, R w * ENNReal.ofReal (1 - acc w) := by rw [h1]
        _ = 1 := h_add
        _ = ENNReal.ofReal (1 - pTerm + pTerm) := by rw [sub_add_cancel, ENNReal.ofReal_one]
        _ = ENNReal.ofReal (1 - pTerm) + ENNReal.ofReal pTerm :=
            ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp0
    calc ∑' w, R w * ENNReal.ofReal (1 - acc w)
        = (ENNReal.ofReal (1 - pTerm) + ENNReal.ofReal pTerm) - ENNReal.ofReal pTerm :=
          ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top h_eq
      _ = ENNReal.ofReal (1 - pTerm) := ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top
  exact ⟨h1, h2, hp0, hp1⟩

lemma valid_step_props {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (P : Measure Dom) [IsProbabilityMeasure P]
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t)
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε)
    (O : List (SimState Out V t) → ℝ)
    (hO : (simAlg u₀ ε β v₀ M outV).IsValidOracle P O)
    {k : ℕ} (hk : k < t) (b : Fin t → V) (h : List (SimState Out V t)) :
    let acc : V → ℝ := fun v => simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))
    let pTerm : ℝ := ∑' v, (M ⟨k, hk⟩ u₀ v).toReal * acc v
    (∀ v, 0 < M ⟨k, hk⟩ u₀ v → 0 ≤ acc v ∧ acc v ≤ 1) ∧
    Summable (fun v => (M ⟨k, hk⟩ u₀ v).toReal * acc v) ∧
    (1 / 2) * Real.exp (-ε) ≤ pTerm ∧ pTerm ≤ Real.exp (-ε) ∧
    ∀ v, |(M ⟨k, hk⟩ u₀ v).toReal * acc v / pTerm - pTarget P (M ⟨k, hk⟩) v| ≤
      3 * simPhi β t * pTarget P (M ⟨k, hk⟩) v := by
  let B := simAlg u₀ ε β v₀ M outV
  set pt : V → ℝ := fun v =>
    sqEstimate (fun u => (M ⟨k, hk⟩ u v).toReal) u₀ ε (O (.active k b v :: h))
  have hpt : ∀ v, 0 < M ⟨k, hk⟩ u₀ v →
      |pt v - pTarget P (M ⟨k, hk⟩) v| ≤ simPhi β t * pTarget P (M ⟨k, hk⟩) v := by
    intro v hq
    have hstep : B.step (.active k b v) =
        .inr (sqQuery (fun u => (M ⟨k, hk⟩ u v).toReal) u₀ ε, simTolerance ε β t,
          fun ans => mixPMF (simAccProb u₀ ε β M ⟨k, hk⟩ v ans)
            (initStage u₀ M outV (k + 1) (Function.update b ⟨k, hk⟩ v))
            (initStage u₀ M outV k b)) := by
      simp [B, simAlg, hk, hq]
    have hans := hO (.active k b v) h _ _ _ hstep
    exact (eq_5_aux P (M ⟨k, hk⟩) (hM_meas ⟨k, hk⟩) u₀ ε β t hε hβ ht (hM_loc ⟨k, hk⟩) v hq
      (O (.active k b v :: h)) hans).2
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    iteration_analysis_aux P (M ⟨k, hk⟩) (hM_meas ⟨k, hk⟩) u₀ ε β t hε hβ hβ1 ht
      (hM_loc ⟨k, hk⟩) pt hpt
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hφ0 : 0 < simPhi β t := by
    unfold simPhi; positivity
  have hφ3 : simPhi β t ≤ 1 / 3 := by
    unfold simPhi; have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hhalf : (1 / 2 : ℝ) ≤ (1 - simPhi β t) / (1 + simPhi β t) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  refine ⟨h1, h2, ?_, h4, h5⟩
  exact (mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le).trans h3

lemma qSum_stageRun_le {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (P : Measure Dom) [IsProbabilityMeasure P]
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t)
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε)
    (O : List (SimState Out V t) → ℝ)
    (hO : (simAlg u₀ ε β v₀ M outV).IsValidOracle P O) :
    ∀ (K : ℕ) (k : ℕ) (b : Fin t → V) (h : List (SimState Out V t)),
      ∑ m ∈ Finset.range K,
        qMass (simAlg u₀ ε β v₀ M outV) (stageRun u₀ ε β v₀ M outV O m k b h) ≤
        ENNReal.ofReal (2 * ((t - k : ℕ) : ℝ) * Real.exp ε)
  | 0, _, _, _ => by simp
  | K + 1, k, b, h => by
    set B := simAlg u₀ ε β v₀ M outV
    rw [Finset.sum_range_succ']
    by_cases hk : k < t
    · obtain ⟨hacc, hsum, hp_lo, _, _⟩ :=
        valid_step_props u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO hk b h
      set acc : V → ℝ := fun v => simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))
      obtain ⟨hw1, hw2, hp0, hp1⟩ := step_weights_sum (M ⟨k, hk⟩ u₀) acc hacc hsum
      set pTerm : ℝ := ∑' v, (M ⟨k, hk⟩ u₀ v).toReal * acc v
      have h_step : ∀ m : ℕ,
          qMass B (stageRun u₀ ε β v₀ M outV O (m + 1) k b h) =
            ∑' v : V,
              (M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) *
                qMass B (stageRun u₀ ε β v₀ M outV O m (k + 1) (Function.update b ⟨k, hk⟩ v)
                  (.active k b v :: h)) +
               M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) *
                qMass B (stageRun u₀ ε β v₀ M outV O m k b (.active k b v :: h))) :=
        fun m => qMass_stageRun_succ_of_lt u₀ ε β v₀ M outV O m hk b h hacc
      have h_inner_le : ∀ v : V,
          (∑ m ∈ Finset.range K,
            (M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) *
              qMass B (stageRun u₀ ε β v₀ M outV O m (k + 1) (Function.update b ⟨k, hk⟩ v)
                (.active k b v :: h)) +
             M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) *
              qMass B (stageRun u₀ ε β v₀ M outV O m k b (.active k b v :: h)))) ≤
          M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) *
            ENNReal.ofReal (2 * ((t - (k + 1) : ℕ) : ℝ) * Real.exp ε) +
          M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) *
            ENNReal.ofReal (2 * ((t - k : ℕ) : ℝ) * Real.exp ε) := by
        intro v
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (qSum_stageRun_le u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO K (k + 1) _ _) zero_le)
          (mul_le_mul_of_nonneg_left
            (qSum_stageRun_le u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO K k _ _) zero_le)
      have h_tsum_le :
          (∑ m ∈ Finset.range K, qMass B (stageRun u₀ ε β v₀ M outV O (m + 1) k b h)) ≤
          ENNReal.ofReal pTerm * ENNReal.ofReal (2 * ((t - (k + 1) : ℕ) : ℝ) * Real.exp ε) +
          ENNReal.ofReal (1 - pTerm) * ENNReal.ofReal (2 * ((t - k : ℕ) : ℝ) * Real.exp ε) := by
        simp_rw [h_step]
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine (ENNReal.tsum_le_tsum h_inner_le).trans ?_
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, hw1, hw2]
      calc (∑ m ∈ Finset.range K, qMass B (stageRun u₀ ε β v₀ M outV O (m + 1) k b h)) +
            qMass B (stageRun u₀ ε β v₀ M outV O 0 k b h)
          ≤ (ENNReal.ofReal pTerm * ENNReal.ofReal (2 * ((t - (k + 1) : ℕ) : ℝ) * Real.exp ε) +
             ENNReal.ofReal (1 - pTerm) * ENNReal.ofReal (2 * ((t - k : ℕ) : ℝ) * Real.exp ε)) +
            ENNReal.ofReal 1 := by
              rw [ENNReal.ofReal_one]
              exact add_le_add h_tsum_le (qMass_le_one B _)
        _ = ENNReal.ofReal
            (pTerm * (2 * ((t - (k + 1) : ℕ) : ℝ) * Real.exp ε) +
             (1 - pTerm) * (2 * ((t - k : ℕ) : ℝ) * Real.exp ε) + 1) := by
              have hA0 : 0 ≤ 2 * ((t - (k + 1) : ℕ) : ℝ) * Real.exp ε := by positivity
              have hB0 : 0 ≤ 2 * ((t - k : ℕ) : ℝ) * Real.exp ε := by positivity
              rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul (sub_nonneg.mpr hp1),
                ← ENNReal.ofReal_add (mul_nonneg hp0 hA0) (mul_nonneg (sub_nonneg.mpr hp1) hB0),
                ← ENNReal.ofReal_add (by positivity) zero_le_one]
        _ ≤ ENNReal.ofReal (2 * ((t - k : ℕ) : ℝ) * Real.exp ε) := by
              apply ENNReal.ofReal_le_ofReal
              have hsub_nat : t - k = (t - (k + 1)) + 1 := by omega
              have hsub : ((t - k : ℕ) : ℝ) = ((t - (k + 1) : ℕ) : ℝ) + 1 := by
                exact_mod_cast hsub_nat
              have hpe : 1 ≤ 2 * pTerm * Real.exp ε := by
                have h1 := mul_le_mul_of_nonneg_right hp_lo (Real.exp_pos ε).le
                have h2 : 1 / 2 * Real.exp (-ε) * Real.exp ε = 1 / 2 := by
                  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
                linarith
              rw [hsub]
              linarith
    · have h0 : qMass B (stageRun u₀ ε β v₀ M outV O 0 k b h) = 0 :=
        qMass_stageRun_zero_of_ge u₀ ε β v₀ M outV O hk b h
      have hsucc : ∀ m, qMass B (stageRun u₀ ε β v₀ M outV O (m + 1) k b h) = 0 := by
        intro m
        rw [stageRun_succ_of_ge u₀ ε β v₀ M outV O m hk, qMass_pure_inl]
      simp only [h0, hsucc, Finset.sum_const_zero, add_zero, zero_le]

lemma expectedQueries_simAlg_le {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (P : Measure Dom) [IsProbabilityMeasure P]
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t)
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε)
    (O : List (SimState Out V t) → ℝ)
    (hO : (simAlg u₀ ε β v₀ M outV).IsValidOracle P O) :
    (simAlg u₀ ε β v₀ M outV).expectedQueries O ≤
      ENNReal.ofReal (2 * t * Real.exp ε) := by
  let B := simAlg u₀ ε β v₀ M outV
  unfold SQAlg.expectedQueries
  refine ENNReal.tsum_le_of_sum_range_le fun K => ?_
  rcases K with _ | K
  · simp
  · rw [Finset.sum_range_succ']
    have h0 : (B.run O 0).toOuterMeasure {c | B.Querying c} = 0 := by
      simp [SQAlg.run, PMF.toOuterMeasure_pure_apply, SQAlg.Querying]
    rw [h0, add_zero]
    simp_rw [run_succ_eq_stageRun u₀ ε β v₀ M outV O]
    have hle := qSum_stageRun_le u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO
      K 0 (fun _ => v₀) []
    rw [Nat.sub_zero] at hle
    exact hle

/-! ### Part 4: Output Probability Lower Bound -/

noncomputable def notDoneMass {Out σ : Type} (D : PMF (Out ⊕ List σ)) : ENNReal :=
  ∑' x : List σ, D (.inr x)

lemma notDoneMass_stageRun_zero {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    (k : ℕ) (b : Fin t → V) (h : List (SimState Out V t)) :
    notDoneMass (stageRun u₀ ε β v₀ M outV O 0 k b h) = 1 := by
  rw [stageRun_zero]
  have h_all : ∑' c : Out ⊕ List (SimState Out V t), stageLaw u₀ M outV k b h c = 1 :=
    PMF.tsum_coe _
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable] at h_all
  have h_inl : (∑' o : Out, stageLaw u₀ M outV k b h (.inl o)) = 0 := by
    simp [stageLaw, PMF.map_apply]
  rw [h_inl, zero_add] at h_all
  exact h_all

lemma notDoneMass_stageRun_succ_of_lt {Dom Out V : Type} {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (O : List (SimState Out V t) → ℝ)
    (N : ℕ) {k : ℕ} (hk : k < t) (b : Fin t → V) (h : List (SimState Out V t))
    (hacc : ∀ v, 0 < M ⟨k, hk⟩ u₀ v →
      0 ≤ simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h)) ∧
      simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h)) ≤ 1) :
    notDoneMass (stageRun u₀ ε β v₀ M outV O (N + 1) k b h) =
      ∑' v : V,
        (M ⟨k, hk⟩ u₀ v *
          ENNReal.ofReal (simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          notDoneMass (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
            (.active k b v :: h)) +
         M ⟨k, hk⟩ u₀ v *
          ENNReal.ofReal (1 - simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))) *
          notDoneMass (stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h))) := by
  unfold notDoneMass
  simp_rw [stageRun_succ_apply_of_lt u₀ ε β v₀ M outV O N hk b h hacc]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun v => ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

noncomputable def pV {Dom V : Type} [MeasurableSpace Dom] {t : ℕ}
    (M : Fin t → Dom → PMF V) (P : Measure Dom) (j : Fin t) (v : V) : ENNReal :=
  ENNReal.ofReal (pTarget P (M j) v)

lemma pV_tsum {Dom V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε : ℝ) (M : Fin t → Dom → PMF V) (P : Measure Dom) [IsProbabilityMeasure P]
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε) (j : Fin t) :
    ∑' v : V, pV M P j v = 1 := by
  unfold pV
  simp_rw [ofReal_pTarget_eq_lintegral P (M j) (hM_meas j)]
  exact lintegral_pmf_tsum P (M j) (hM_meas j) u₀ ε (hM_loc j)

noncomputable def targetMass {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out) (P : Measure Dom)
    (k : ℕ) (b : Fin t → V) (o : Out) : ENNReal :=
  by
    classical
    exact ∑' b' : Fin t → V,
      if outV b' = o ∧ ∀ j : Fin t, j.val < k → b' j = b j then
        ∏ j : Fin t, (if k ≤ j.val then pV M P j (b' j) else 1)
      else 0

lemma targetMass_of_ge {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out) (P : Measure Dom)
    {k : ℕ} (hk : ¬ k < t) (b : Fin t → V) (o : Out) :
    targetMass M outV P k b o = by classical exact if outV b = o then 1 else 0 := by
  classical
  unfold targetMass
  have h_cond : ∀ b' : Fin t → V,
      (if outV b' = o ∧ ∀ j : Fin t, j.val < k → b' j = b j then
        ∏ j : Fin t, (if k ≤ j.val then pV M P j (b' j) else 1)
      else 0) = if b' = b then (if outV b = o then 1 else 0) else 0 := by
    intro b'
    have hlt : ∀ j : Fin t, j.val < k := fun j => lt_of_lt_of_le j.isLt (not_lt.mp hk)
    have hge : ∀ j : Fin t, ¬ k ≤ j.val := fun j => not_le.mpr (hlt j)
    have h_eq : (∀ j : Fin t, j.val < k → b' j = b j) ↔ b' = b := by
      simp [hlt, funext_iff]
    simp [hge, h_eq]
    by_cases hb : b' = b <;> simp [hb]
  simp_rw [h_cond, tsum_ite_eq]

lemma targetMass_of_lt {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out) (P : Measure Dom)
    {k : ℕ} (hk : k < t) (b : Fin t → V) (o : Out) :
    targetMass M outV P k b o =
      ∑' v : V, pV M P ⟨k, hk⟩ v *
        targetMass M outV P (k + 1) (Function.update b ⟨k, hk⟩ v) o := by
  classical
  unfold targetMass
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b' => ?_
  have h_inner : ∀ v : V,
      pV M P ⟨k, hk⟩ v *
        (if outV b' = o ∧ ∀ j : Fin t, j.val < k + 1 → b' j = Function.update b ⟨k, hk⟩ v j then
          ∏ j : Fin t, (if k + 1 ≤ j.val then pV M P j (b' j) else 1)
        else 0) =
      if v = b' ⟨k, hk⟩ then
        (if outV b' = o ∧ ∀ j : Fin t, j.val < k → b' j = b j then
          ∏ j : Fin t, (if k ≤ j.val then pV M P j (b' j) else 1)
        else 0)
      else 0 := by
    intro v
    have h_upd_iff :
        (∀ j : Fin t, j.val < k + 1 → b' j = Function.update b ⟨k, hk⟩ v j) ↔
          v = b' ⟨k, hk⟩ ∧ (∀ j : Fin t, j.val < k → b' j = b j) := by
      constructor
      · intro h
        refine ⟨?_, fun j hj => ?_⟩
        · have hk1 := h ⟨k, hk⟩ (Nat.lt_succ_self k)
          simpa using hk1.symm
        · have hj1 := h j (Nat.lt_succ_of_lt hj)
          have hne : j ≠ ⟨k, hk⟩ := Fin.ne_of_lt hj
          rwa [Function.update_of_ne hne] at hj1
      · rintro ⟨rfl, hj_lt⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · have hne : j ≠ ⟨k, hk⟩ := Fin.ne_of_lt hlt
          rw [Function.update_of_ne hne]
          exact hj_lt j hlt
        · have hjeq : j = ⟨k, hk⟩ := Fin.ext heq
          subst hjeq
          simp
    have h_prod :
        pV M P ⟨k, hk⟩ (b' ⟨k, hk⟩) *
          (∏ j : Fin t, (if k + 1 ≤ j.val then pV M P j (b' j) else 1)) =
        ∏ j : Fin t, (if k ≤ j.val then pV M P j (b' j) else 1) := by
      have hL := Finset.mul_prod_erase Finset.univ
        (fun j : Fin t => if k + 1 ≤ j.val then pV M P j (b' j) else 1)
        (Finset.mem_univ (⟨k, hk⟩ : Fin t))
      have hR := Finset.mul_prod_erase Finset.univ
        (fun j : Fin t => if k ≤ j.val then pV M P j (b' j) else 1)
        (Finset.mem_univ (⟨k, hk⟩ : Fin t))
      rw [← hL, ← hR]
      have hk1 : ¬ k + 1 ≤ (⟨k, hk⟩ : Fin t).val := by simp
      have hk0 : k ≤ (⟨k, hk⟩ : Fin t).val := le_rfl
      simp only [hk1, hk0, ite_false, ite_true, one_mul]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have hne : j.val ≠ k := fun hval =>
        (Finset.ne_of_mem_erase hj) (Fin.ext hval)
      have h_iff : k + 1 ≤ j.val ↔ k ≤ j.val := by omega
      simp [h_iff]
    simp only [h_upd_iff]
    by_cases hv : v = b' ⟨k, hk⟩
    · subst hv
      by_cases hcond : outV b' = o ∧ ∀ j : Fin t, j.val < k → b' j = b j
      · simp only [hcond, true_and, ite_true]
        rw [if_pos hcond.2, if_pos hcond.2, h_prod]
      · simp [hcond]
    · simp [hv]
  simp_rw [h_inner, tsum_ite_eq]

lemma targetMass_tsum_aux {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε : ℝ) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (P : Measure Dom) [IsProbabilityMeasure P]
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε) :
    ∀ (m : ℕ) (k : ℕ), t - k = m → ∀ b : Fin t → V,
      ∑' o : Out, targetMass M outV P k b o = 1
  | 0, k, hm, b => by
    classical
    have hk : ¬ k < t := by omega
    simp_rw [targetMass_of_ge M outV P hk b]
    simp
  | m + 1, k, hm, b => by
    have hk : k < t := by omega
    have hm' : t - (k + 1) = m := by omega
    simp_rw [targetMass_of_lt M outV P hk b]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left,
      targetMass_tsum_aux u₀ ε M outV P hM_meas hM_loc m (k + 1) hm', mul_one]
    exact pV_tsum u₀ ε M P hM_meas hM_loc ⟨k, hk⟩

lemma targetMass_tsum {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε : ℝ) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (P : Measure Dom) [IsProbabilityMeasure P]
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε) (k : ℕ) (b : Fin t → V) :
    ∑' o : Out, targetMass M outV P k b o = 1 :=
  targetMass_tsum_aux u₀ ε M outV P hM_meas hM_loc (t - k) k rfl b

lemma targetMass_le_one {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε : ℝ) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (P : Measure Dom) [IsProbabilityMeasure P]
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε) (k : ℕ) (b : Fin t → V) (o : Out) :
    targetMass M outV P k b o ≤ 1 :=
  (ENNReal.le_tsum o).trans (targetMass_tsum u₀ ε M outV P hM_meas hM_loc k b).le

lemma stageRun_output_lower_bound {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (P : Measure Dom) [IsProbabilityMeasure P]
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t)
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε)
    (O : List (SimState Out V t) → ℝ)
    (hO : (simAlg u₀ ε β v₀ M outV).IsValidOracle P O) (o : Out) :
    ∀ (N : ℕ) (k : ℕ) (b : Fin t → V) (h : List (SimState Out V t)),
      ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - k)) * targetMass M outV P k b o ≤
        stageRun u₀ ε β v₀ M outV O N k b h (.inl o) +
        notDoneMass (stageRun u₀ ε β v₀ M outV O N k b h)
  | 0, k, b, h => by
    rw [notDoneMass_stageRun_zero]
    have htr : (0 : ℝ) < t := by exact_mod_cast ht
    have hφ0 : 0 ≤ simPhi β t := by
      unfold simPhi; positivity
    have hφ3 : simPhi β t ≤ 1 / 3 := by
      unfold simPhi; have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hpow : (1 - 3 * simPhi β t) ^ (t - k) ≤ 1 :=
      pow_le_one₀ (by linarith) (by linarith)
    calc ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - k)) * targetMass M outV P k b o
        ≤ 1 * 1 := mul_le_mul (ENNReal.ofReal_le_one.mpr hpow)
          (targetMass_le_one u₀ ε M outV P hM_meas hM_loc k b o) zero_le zero_le
      _ = 1 := mul_one 1
      _ ≤ stageRun u₀ ε β v₀ M outV O 0 k b h (.inl o) + 1 := le_add_self
  | N + 1, k, b, h => by
    classical
    by_cases hk : k < t
    · obtain ⟨hacc, hsum, hp_lo, _, hratio⟩ :=
        valid_step_props u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO hk b h
      set acc : V → ℝ := fun v => simAccProb u₀ ε β M ⟨k, hk⟩ v (O (.active k b v :: h))
      obtain ⟨_, hw2, hp0, hp1⟩ := step_weights_sum (M ⟨k, hk⟩ u₀) acc hacc hsum
      set pTerm : ℝ := ∑' v, (M ⟨k, hk⟩ u₀ v).toReal * acc v
      have hp_pos : 0 < pTerm := lt_of_lt_of_le (by positivity) hp_lo
      have htr : (0 : ℝ) < t := by exact_mod_cast ht
      have hφ0 : 0 ≤ simPhi β t := by
        unfold simPhi; positivity
      have hφ3 : simPhi β t ≤ 1 / 3 := by
        unfold simPhi; have : (1 : ℝ) ≤ t := by exact_mod_cast ht
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have h1m3φ : 0 ≤ 1 - 3 * simPhi β t := by linarith
      rw [stageRun_succ_apply_of_lt u₀ ε β v₀ M outV O N hk b h hacc (.inl o),
        notDoneMass_stageRun_succ_of_lt u₀ ε β v₀ M outV O N hk b h hacc,
        ← ENNReal.tsum_add]
      have h_acc_ge : ∀ v : V,
          ENNReal.ofReal pTerm * ENNReal.ofReal (1 - 3 * simPhi β t) * pV M P ⟨k, hk⟩ v ≤
            M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) := by
        intro v
        by_cases hv : 0 < M ⟨k, hk⟩ u₀ v
        · have h_abs := (abs_le.mp (hratio v)).1
          have h_div : (1 - 3 * simPhi β t) * pTarget P (M ⟨k, hk⟩) v ≤
              (M ⟨k, hk⟩ u₀ v).toReal * acc v / pTerm := by linarith
          have h_mul : pTerm * (1 - 3 * simPhi β t) * pTarget P (M ⟨k, hk⟩) v ≤
              (M ⟨k, hk⟩ u₀ v).toReal * acc v := by
            rw [le_div_iff₀ hp_pos] at h_div
            linarith
          unfold pV
          rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul (mul_nonneg hp0 h1m3φ),
            ← ENNReal.ofReal_toReal (PMF.apply_ne_top (M ⟨k, hk⟩ u₀) v),
            ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
          exact ENNReal.ofReal_le_ofReal h_mul
        · have hz : M ⟨k, hk⟩ u₀ v = 0 := le_antisymm (not_lt.mp hv) bot_le
          have hpz : pV M P ⟨k, hk⟩ v = 0 := by
            unfold pV
            rw [ofReal_pTarget_eq_lintegral P (M ⟨k, hk⟩) (hM_meas ⟨k, hk⟩)]
            have h0 : ∀ u, M ⟨k, hk⟩ u v = 0 := fun u =>
              le_antisymm ((hM_loc ⟨k, hk⟩ u u₀ v).trans (by simp [hz])) bot_le
            simp [h0]
          simp [hz, hpz]
      have h_sub_succ : t - k = (t - (k + 1)) + 1 := by omega
      have h_pow_split :
          ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - k)) =
            ENNReal.ofReal (1 - 3 * simPhi β t) *
              ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - (k + 1))) := by
        rw [h_sub_succ, pow_succ', ENNReal.ofReal_mul h1m3φ]
      set L := ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - k)) * targetMass M outV P k b o
      have h_term_ge : ∀ v : V,
          ENNReal.ofReal pTerm * ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - k)) *
            (pV M P ⟨k, hk⟩ v *
              targetMass M outV P (k + 1) (Function.update b ⟨k, hk⟩ v) o) +
          M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) * L ≤
          (M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) *
            stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
              (.active k b v :: h) (.inl o) +
           M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) *
            stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h) (.inl o)) +
          (M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) *
            notDoneMass (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
              (.active k b v :: h)) +
           M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) *
            notDoneMass (stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h))) := by
        intro v
        have ih1 := stageRun_output_lower_bound u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO o
          N (k + 1) (Function.update b ⟨k, hk⟩ v) (.active k b v :: h)
        have ih2 := stageRun_output_lower_bound u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO o
          N k b (.active k b v :: h)
        have h_rearr :
            (M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) *
              stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
                (.active k b v :: h) (.inl o) +
             M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) *
              stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h) (.inl o)) +
            (M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) *
              notDoneMass (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
                (.active k b v :: h)) +
             M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) *
              notDoneMass (stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h))) =
            M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v) *
              (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
                (.active k b v :: h) (.inl o) +
               notDoneMass (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
                (.active k b v :: h))) +
            M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (1 - acc v) *
              (stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h) (.inl o) +
               notDoneMass (stageRun u₀ ε β v₀ M outV O N k b (.active k b v :: h))) := by ring
        rw [h_rearr]
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left ih2 zero_le)
        calc ENNReal.ofReal pTerm * ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - k)) *
              (pV M P ⟨k, hk⟩ v *
                targetMass M outV P (k + 1) (Function.update b ⟨k, hk⟩ v) o)
            = (ENNReal.ofReal pTerm * ENNReal.ofReal (1 - 3 * simPhi β t) * pV M P ⟨k, hk⟩ v) *
              (ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - (k + 1))) *
                targetMass M outV P (k + 1) (Function.update b ⟨k, hk⟩ v) o) := by
                rw [h_pow_split]; ring
          _ ≤ (M ⟨k, hk⟩ u₀ v * ENNReal.ofReal (acc v)) *
              (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
                (.active k b v :: h) (.inl o) +
               notDoneMass (stageRun u₀ ε β v₀ M outV O N (k + 1) (Function.update b ⟨k, hk⟩ v)
                (.active k b v :: h))) :=
                mul_le_mul (h_acc_ge v) ih1 zero_le zero_le
      refine le_trans ?_ (ENNReal.tsum_le_tsum h_term_ge)
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← targetMass_of_lt M outV P hk b o,
        ENNReal.tsum_mul_right, hw2]
      have hp_sum1 : ENNReal.ofReal pTerm + ENNReal.ofReal (1 - pTerm) = 1 := by
        rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1), add_sub_cancel, ENNReal.ofReal_one]
      exact le_of_eq <| calc L = 1 * L := (one_mul L).symm
        _ = (ENNReal.ofReal pTerm + ENNReal.ofReal (1 - pTerm)) * L := by rw [hp_sum1]
        _ = ENNReal.ofReal pTerm *
              (ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - k)) * targetMass M outV P k b o) +
            ENNReal.ofReal (1 - pTerm) * L := by rw [add_mul]
        _ = ENNReal.ofReal pTerm * ENNReal.ofReal ((1 - 3 * simPhi β t) ^ (t - k)) *
              targetMass M outV P k b o +
            ENNReal.ofReal (1 - pTerm) * L := by rw [mul_assoc]
    · have hsub : t - k = 0 := Nat.sub_eq_zero_of_le (not_lt.mp hk)
      rw [hsub, pow_zero, ENNReal.ofReal_one, one_mul, targetMass_of_ge M outV P hk b o,
        stageRun_succ_of_ge u₀ ε β v₀ M outV O N hk b h]
      by_cases ho : outV b = o
      · subst ho
        simp
      · have hne : o ≠ outV b := Ne.symm ho
        simp [ho, hne]

/-! ### Part 5: Connecting `notDoneMass` to `qMass` and Passing to `outputLaw` -/

lemma next_inr_nil {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ) (c : Out ⊕ List σ) :
    B.next O c (.inr []) = 0 := by
  rcases c with o | (_ | ⟨s, h⟩)
  · simp [SQAlg.next]
  · simp [SQAlg.next, PMF.map_apply]
  · dsimp [SQAlg.next]
    rcases B.step s with o | ⟨g, τ, k⟩ <;> simp [PMF.map_apply]

lemma run_inr_nil_of_pos {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    B.run O N (.inr []) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
  simp [SQAlg.run, PMF.bind_apply, next_inr_nil]

lemma notDoneMass_next_le {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ)
    (c : Out ⊕ List σ) (hc : c ≠ .inr []) :
    notDoneMass (B.next O c) ≤ by classical exact if B.Querying c then 1 else 0 := by
  classical
  rcases c with o | (_ | ⟨s, h⟩)
  · simp [notDoneMass, SQAlg.next, SQAlg.Querying]
  · exact (hc rfl).elim
  · rcases hstep : B.step s with o | ⟨g, τ, k⟩
    · simp [notDoneMass, SQAlg.next, SQAlg.Querying, hstep]
    · simp only [SQAlg.next, SQAlg.Querying, hstep, Sum.isRight_inr, ite_true]
      set D : PMF (Out ⊕ List σ) := (k (O (s :: h))).map (fun s' => Sum.inr (s' :: s :: h))
      calc notDoneMass D
          ≤ ∑' y : Out ⊕ List σ, D y :=
            ENNReal.tsum_comp_le_tsum_of_injective Sum.inr_injective D
        _ = 1 := PMF.tsum_coe D

lemma notDoneMass_run_succ_le_qMass {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    notDoneMass (B.run O (N + 1)) ≤ qMass B (B.run O N) := by
  classical
  unfold notDoneMass qMass
  simp only [SQAlg.run, PMF.bind_apply, PMF.toOuterMeasure_apply]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun c => ?_
  by_cases hc : c = .inr []
  · subst hc
    rw [run_inr_nil_of_pos B O hN, zero_mul]
    exact zero_le
  · refine (mul_le_mul_of_nonneg_left (notDoneMass_next_le B O c hc) zero_le).trans ?_
    by_cases hq : B.Querying c
    · simp [hq]
    · simp [hq]

lemma le_of_le_add_of_tsum_ne_top {L U : ENNReal} {a : ℕ → ENNReal}
    (ha : ∑' n, a n ≠ ⊤) (h : ∀ n ≥ 1, L ≤ U + a n) : L ≤ U := by
  by_contra! hlt
  have h1 : ∑' _ : ℕ, (L - U) = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero (tsub_pos_of_lt hlt).ne'
  have h2 : ∑' _ : ℕ, (L - U) ≤ ∑' n : ℕ, a n :=
    (ENNReal.tsum_le_tsum fun n => tsub_le_iff_left.mpr (h (n + 1) (Nat.le_add_left 1 n))).trans
      (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 1) a)
  exact ha (top_unique (h1 ▸ h2))

lemma outputLaw_simAlg_ge {Dom Out V : Type} [MeasurableSpace Dom] {t : ℕ}
    (u₀ : Dom) (ε β : ℝ) (v₀ : V) (M : Fin t → Dom → PMF V) (outV : (Fin t → V) → Out)
    (P : Measure Dom) [IsProbabilityMeasure P]
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t)
    (hM_meas : ∀ k v, Measurable fun u => M k u v)
    (hM_loc : ∀ k, IsLocalRandomizerPMF (M k) ε)
    (O : List (SimState Out V t) → ℝ)
    (hO : (simAlg u₀ ε β v₀ M outV).IsValidOracle P O) (o : Out) :
    ENNReal.ofReal ((1 - 3 * simPhi β t) ^ t) * targetMass M outV P 0 (fun _ => v₀) o ≤
      (simAlg u₀ ε β v₀ M outV).outputLaw O o := by
  let B := simAlg u₀ ε β v₀ M outV
  have h_qsum_ne_top : ∑' N : ℕ, qMass B (B.run O N) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt
      (expectedQueries_simAlg_le u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO)
      ENNReal.ofReal_lt_top)
  refine le_of_le_add_of_tsum_ne_top h_qsum_ne_top fun N hN => ?_
  have h_lb := stageRun_output_lower_bound u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO o
    N 0 (fun _ => v₀) []
  rw [Nat.sub_zero, ← run_succ_eq_stageRun] at h_lb
  refine h_lb.trans (add_le_add ?_ (notDoneMass_run_succ_le_qMass B O hN))
  exact le_iSup (fun M => B.run O M (.inl o)) (N + 1)

lemma outputLaw_tsum_le_one {Dom Out σ : Type} (B : SQAlg Dom Out σ) (O : List σ → ℝ) :
    ∑' o : Out, B.outputLaw O o ≤ 1 := by
  have hmono : ∀ o : Out, Monotone (fun N => B.run O N (.inl o)) := by
    intro o
    refine monotone_nat_of_le_succ fun N => ?_
    calc B.run O N (.inl o)
        = B.run O N (.inl o) * B.next O (.inl o) (.inl o) := by simp [SQAlg.next]
      _ ≤ ∑' c, B.run O N c * B.next O c (.inl o) :=
          ENNReal.le_tsum (f := fun c => B.run O N c * B.next O c (.inl o)) (.inl o)
      _ = B.run O (N + 1) (.inl o) := by simp [SQAlg.run, PMF.bind_apply]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  unfold SQAlg.outputLaw
  rw [ENNReal.finsetSum_iSup_of_monotone hmono]
  refine iSup_le fun N => ?_
  calc ∑ o ∈ F, B.run O N (.inl o)
      ≤ ∑' o : Out, B.run O N (.inl o) := ENNReal.sum_le_tsum F
    _ ≤ ∑' c : Out ⊕ List σ, B.run O N c :=
        ENNReal.tsum_comp_le_tsum_of_injective Sum.inl_injective (B.run O N)
    _ = 1 := PMF.tsum_coe (B.run O N)

/-! ### Part 6: Bernoulli Inequality and Statistical Difference Bound -/

lemma bernoulli_sub : ∀ (m : ℕ) (x : ℝ), 0 ≤ x → x ≤ 1 → 1 - (m : ℝ) * x ≤ (1 - x) ^ m
  | 0, _, _, _ => by simp
  | m + 1, x, hx0, hx1 => by
    have ih := bernoulli_sub m x hx0 hx1
    have hmul : (1 - (m : ℝ) * x) * (1 - x) ≤ (1 - x) ^ m * (1 - x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hmx2 : 0 ≤ (m : ℝ) * (x * x) := by positivity
    rw [pow_succ]
    push_cast
    linarith

lemma statDiff_le_of_pointwise_ge {Out : Type*} (μ ν : Out → ENNReal) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hμ : ∑' o, μ o ≤ 1) (hν : ∑' o, ν o = 1)
    (hge : ∀ o, ENNReal.ofReal (1 - β) * ν o ≤ μ o) :
    statDiff μ ν ≤ ENNReal.ofReal β := by
  classical
  unfold statDiff
  refine iSup_le fun S => ?_
  set A_S := ∑' o, S.indicator μ o
  set A_Sc := ∑' o, Sᶜ.indicator μ o
  set B_S := ∑' o, S.indicator ν o
  set B_Sc := ∑' o, Sᶜ.indicator ν o
  have h_ind_compl : ∀ (f : Out → ENNReal) (o : Out), S.indicator f o + Sᶜ.indicator f o = f o := by
    intro f o; by_cases ho : o ∈ S <;> simp [ho]
  have hA_split : A_S + A_Sc = ∑' o, μ o := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr (h_ind_compl μ)
  have hB_split : B_S + B_Sc = 1 := by
    rw [← ENNReal.tsum_add, tsum_congr (h_ind_compl ν), hν]
  have hA_le : A_S + A_Sc ≤ 1 := hA_split ▸ hμ
  have hB_S_le : B_S ≤ 1 := (le_self_add : B_S ≤ B_S + B_Sc).trans hB_split.le
  have hB_Sc_le : B_Sc ≤ 1 := (le_add_self : B_Sc ≤ B_S + B_Sc).trans hB_split.le
  have h1mβ : ENNReal.ofReal (1 - β) + ENNReal.ofReal β = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hβ1) hβ0, sub_add_cancel, ENNReal.ofReal_one]
  have hge_S : ENNReal.ofReal (1 - β) * B_S ≤ A_S := by
    dsimp [B_S, A_S]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun o => ?_
    by_cases ho : o ∈ S <;> simp [ho, hge o]
  have hge_Sc : ENNReal.ofReal (1 - β) * B_Sc ≤ A_Sc := by
    dsimp [B_Sc, A_Sc]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun o => ?_
    by_cases ho : o ∈ S <;> simp [ho, hge o]
  have h_BS_le : B_S ≤ A_S + ENNReal.ofReal β := by
    calc B_S = 1 * B_S := (one_mul B_S).symm
      _ = (ENNReal.ofReal (1 - β) + ENNReal.ofReal β) * B_S := by rw [h1mβ]
      _ = ENNReal.ofReal (1 - β) * B_S + ENNReal.ofReal β * B_S := add_mul _ _ _
      _ ≤ A_S + ENNReal.ofReal β * 1 :=
          add_le_add hge_S (mul_le_mul_of_nonneg_left hB_S_le zero_le)
      _ = A_S + ENNReal.ofReal β := by rw [mul_one]
  have h_AS_le : A_S ≤ B_S + ENNReal.ofReal β := by
    have h1 : A_S + ENNReal.ofReal (1 - β) * B_Sc ≤ B_S + B_Sc := by
      calc A_S + ENNReal.ofReal (1 - β) * B_Sc
          ≤ A_S + A_Sc := add_le_add le_rfl hge_Sc
        _ ≤ 1 := hA_le
        _ = B_S + B_Sc := hB_split.symm
    have h2 : B_S + B_Sc ≤ B_S + ENNReal.ofReal β + ENNReal.ofReal (1 - β) * B_Sc := by
      calc B_S + B_Sc = B_S + 1 * B_Sc := by rw [one_mul]
        _ = B_S + (ENNReal.ofReal β + ENNReal.ofReal (1 - β)) * B_Sc := by
            rw [add_comm (ENNReal.ofReal β), h1mβ]
        _ = B_S + ENNReal.ofReal β * B_Sc + ENNReal.ofReal (1 - β) * B_Sc := by
            rw [add_mul, add_assoc]
        _ ≤ B_S + ENNReal.ofReal β * 1 + ENNReal.ofReal (1 - β) * B_Sc :=
            add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hB_Sc_le zero_le)) le_rfl
        _ = B_S + ENNReal.ofReal β + ENNReal.ofReal (1 - β) * B_Sc := by rw [mul_one]
    have hfin : ENNReal.ofReal (1 - β) * B_Sc ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_of_lt (lt_of_le_of_lt hB_Sc_le ENNReal.one_lt_top))
    exact (ENNReal.add_le_add_iff_right hfin).mp (h1.trans h2)
  rcases le_total A_S B_S with hle | hle
  · rw [tsub_eq_zero_of_le hle, zero_add]
    exact tsub_le_iff_left.mpr h_BS_le
  · rw [tsub_eq_zero_of_le hle, add_zero]
    exact tsub_le_iff_left.mpr h_AS_le

end Aux_Claim59

open Aux_Claim59 in
theorem solution :
    ∀ (Dom W Out : Type) [MeasurableSpace Dom] (n t : ℕ) (ε β : ℝ) (_ : Dom),
      0 < ε → 0 < β → β ≤ 1 → 1 ≤ t →
      ∀ A : LocalAlg Dom W Out n t ε, A.IsNoninteractive →
        ∃ (σ : Type) (B : SQAlg Dom Out σ),
          B.AsksOnly (simTolerance ε β t) ∧
          ∀ (P : Measure Dom) [IsProbabilityMeasure P] (O : List σ → ℝ),
            B.IsValidOracle P O →
              B.expectedQueries O ≤ ENNReal.ofReal (2 * t * Real.exp ε) ∧
              statDiff (B.outputLaw O) (A.iidOutputLaw P) ≤ ENNReal.ofReal β := by
  classical
  intro Dom W Out _ n t ε β u₀ hε hβ hβ1 ht A hNI
  obtain ⟨w₀, _⟩ := (A.R ⟨0, ht⟩ Fin.elim0 u₀).support_nonempty
  set idx₀ : Fin t → Fin n := fun k => A.idx k (fun _ => w₀)
  set R₀ : Fin t → Dom → PMF W := fun k => A.R k (fun _ => w₀)
  set eps₀ : Fin t → ℝ := fun k => A.eps k (fun _ => w₀)
  have h_idx : ∀ k a, A.idx k a = idx₀ k := fun k a => (hNI k a (fun _ => w₀)).1
  have h_R : ∀ k a, A.R k a = R₀ k := fun k a => (hNI k a (fun _ => w₀)).2.1
  have h_eps : ∀ k a, A.eps k a = eps₀ k := fun k a => (hNI k a (fun _ => w₀)).2.2
  have heps_nonneg : ∀ j : Fin t, 0 ≤ eps₀ j := by
    intro j
    obtain ⟨wj, hwj⟩ := (R₀ j u₀).support_nonempty
    have hne0 : R₀ j u₀ wj ≠ 0 := (PMF.mem_support_iff _ _).mp hwj
    have hpos : 0 < (R₀ j u₀ wj).toReal :=
      ENNReal.toReal_pos hne0 (PMF.apply_ne_top _ _)
    have hloc := loc_real (R₀ j) (eps₀ j) (A.isLocal j (fun _ => w₀)) u₀ u₀ wj
    have h1 : 1 * (R₀ j u₀ wj).toReal ≤ Real.exp (eps₀ j) * (R₀ j u₀ wj).toReal := by linarith
    have h2 : 1 ≤ Real.exp (eps₀ j) := le_of_mul_le_mul_right h1 hpos
    exact Real.exp_le_exp.mp (by rwa [Real.exp_zero])
  have h_min_eq : ∀ (s₁ s₂ : Finset (Fin t)) (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty),
      s₁ = s₂ → s₁.min' h₁ = s₂.min' h₂ := by
    rintro s _ h₁ h₂ rfl
    rfl
  set leaderOf : Fin t → Fin t := fun j =>
    (Finset.univ.filter (fun k : Fin t => idx₀ k = idx₀ j)).min'
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩⟩
  have h_leader_idx : ∀ j : Fin t, idx₀ (leaderOf j) = idx₀ j := by
    intro j
    have hmem := Finset.min'_mem (Finset.univ.filter (fun k : Fin t => idx₀ k = idx₀ j))
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩⟩
    exact (Finset.mem_filter.mp hmem).2
  have h_leader_idem : ∀ j : Fin t, leaderOf (leaderOf j) = leaderOf j := by
    intro j
    apply h_min_eq
    ext k
    simp [h_leader_idx j]
  have h_leader_eq_iff : ∀ k j : Fin t, leaderOf k = k → (leaderOf j = k ↔ idx₀ j = idx₀ k) := by
    intro k j hk
    constructor
    · rintro rfl; exact (h_leader_idx j).symm
    · intro hidx
      rw [← hk]
      apply h_min_eq
      ext m
      simp [hidx]
  have h_leader_ne : ∀ k j : Fin t, leaderOf k ≠ k → leaderOf j ≠ k := by
    intro k j hk hjk
    apply hk
    rw [← hjk, h_leader_idem j]
  set M : Fin t → Dom → PMF (Fin t → W) := fun k u =>
    pmfPi (fun j : Fin t => if leaderOf j = k then R₀ j u else PMF.pure w₀)
  set reassemble : (Fin t → (Fin t → W)) → (Fin t → W) := fun b j => b (leaderOf j) j
  set embed : (Fin t → W) → (Fin t → (Fin t → W)) := fun a k j =>
    if leaderOf j = k then a j else w₀
  set outV : (Fin t → (Fin t → W)) → Out := fun b => A.out (reassemble b)
  set v₀ : Fin t → W := fun _ => w₀
  have h_reassemble_embed : ∀ a : Fin t → W, reassemble (embed a) = a := by
    intro a
    ext j
    simp [reassemble, embed]
  have h_embed_inj : Function.Injective embed :=
    Function.LeftInverse.injective h_reassemble_embed
  have hM_meas : ∀ (k : Fin t) (v : Fin t → W), Measurable fun u => M k u v := by
    intro k v
    have h_eq : (fun u => M k u v) =
        fun u => ∏ j : Fin t, (if leaderOf j = k then R₀ j u (v j) else (PMF.pure w₀) (v j)) := by
      ext u
      rw [pmfPi_apply]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hjk : leaderOf j = k <;> simp [hjk]
    rw [h_eq]
    refine Finset.measurable_prod Finset.univ fun j _ => ?_
    by_cases hjk : leaderOf j = k
    · simp only [hjk, ite_true]
      exact A.measurable_R j (fun _ => w₀) (v j)
    · simp only [hjk, ite_false]
      exact measurable_const
  have hM_loc : ∀ k : Fin t, IsLocalRandomizerPMF (M k) ε := by
    intro k u u' v
    rw [pmfPi_apply, pmfPi_apply]
    set ej : Fin t → ℝ := fun j => if leaderOf j = k then eps₀ j else 0
    have h_factor : ∀ j : Fin t,
        (if leaderOf j = k then R₀ j u else PMF.pure w₀) (v j) ≤
          ENNReal.ofReal (Real.exp (ej j)) *
            (if leaderOf j = k then R₀ j u' else PMF.pure w₀) (v j) := by
      intro j
      dsimp [ej]
      by_cases hjk : leaderOf j = k
      · simp only [hjk, ite_true]
        exact A.isLocal j (fun _ => w₀) u u' (v j)
      · simp [hjk]
    have h_prod := Finset.prod_le_prod' (s := Finset.univ) (fun j _ => h_factor j)
    rw [Finset.prod_mul_distrib,
      ← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
      ← Real.exp_sum] at h_prod
    refine h_prod.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) zero_le)
    by_cases hk : leaderOf k = k
    · have h_sum : (∑ j : Fin t, ej j) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin t => A.idx j (histPrefix (fun _ => w₀) j) = idx₀ k),
            A.eps j (histPrefix (fun _ => w₀) j) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun j _ => (h_eps j _).symm)
        ext j
        simp [h_idx, h_leader_eq_iff k j hk]
      rw [h_sum]
      exact A.budget (fun _ => w₀) (idx₀ k)
    · have h0 : ∀ j : Fin t, ej j = 0 := fun j => if_neg (h_leader_ne k j hk)
      simp [h0, hε.le]
  refine ⟨SimState Out (Fin t → W) t, simAlg u₀ ε β v₀ M outV,
    simAlg_asksOnly u₀ ε β v₀ M outV hε hM_meas hM_loc, ?_⟩
  intro P _ O hO
  refine ⟨expectedQueries_simAlg_le u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO, ?_⟩
  have h_target_eq_iid : ∀ o : Out, targetMass M outV P 0 (fun _ => v₀) o = A.iidOutputLaw P o := by
    intro o
    have h_t0 : targetMass M outV P 0 (fun _ => v₀) o =
        ∑' b : Fin t → (Fin t → W),
          if outV b = o then ∏ k : Fin t, (∫⁻ u, M k u (b k) ∂P) else 0 := by
      unfold targetMass
      refine tsum_congr fun b => ?_
      simp [pV, ofReal_pTarget_eq_lintegral P (M _) (hM_meas _)]
    rw [h_t0]
    set F : (Fin t → (Fin t → W)) → ENNReal := fun b =>
      if outV b = o then ∏ k : Fin t, (∫⁻ u, M k u (b k) ∂P) else 0
    have hF_supp : Function.support F ⊆ Set.range embed := by
      intro b hb
      by_contra hnot
      apply hb
      dsimp [F]
      have hne : b ≠ embed (reassemble b) := fun heq => hnot ⟨reassemble b, heq.symm⟩
      have hex : ∃ k j : Fin t, b k j ≠ embed (reassemble b) k j := by
        by_contra! hall
        exact hne (funext fun k => funext fun j => hall k j)
      rcases hex with ⟨k, j, hkj⟩
      have hjk : leaderOf j ≠ k := by
        intro hjk_eq
        apply hkj
        simp [embed, reassemble, hjk_eq]
      have hbw0 : b k j ≠ w₀ := by
        simpa [embed, hjk] using hkj
      have hMk0 : ∀ u : Dom, M k u (b k) = 0 := by
        intro u
        rw [pmfPi_apply]
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjk, PMF.pure_apply, hbw0])
      have hprod0 : (∏ k' : Fin t, ∫⁻ u, M k' u (b k') ∂P) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hMk0])
      simp [hprod0]
    rw [← h_embed_inj.tsum_eq hF_supp]
    unfold LocalAlg.iidOutputLaw
    refine tsum_congr fun a => ?_
    have h_out_embed : outV (embed a) = A.out a := by
      dsimp [outV]
      rw [h_reassemble_embed a]
    dsimp only [F]
    simp only [h_out_embed]
    have h_prod_lint :
        (∏ k : Fin t, ∫⁻ u, M k u (embed a k) ∂P) =
          ∫⁻ z : Fin n → Dom, A.transcriptMass z a ∂(Measure.pi fun _ : Fin n => P) := by
      set f : Fin t → Dom → ENNReal := fun k u => M k u (embed a k)
      have hf_meas : ∀ k, Measurable (f k) := fun k => hM_meas k (embed a k)
      have hf_nonleader : ∀ k : Fin t, leaderOf k ≠ k → ∀ u, f k u = 1 := by
        intro k hk u
        dsimp [f, M, embed]
        rw [pmfPi_apply]
        refine Finset.prod_eq_one fun j _ => ?_
        have hjk : leaderOf j ≠ k := h_leader_ne k j hk
        simp [hjk]
      have h_tmass : ∀ z : Fin n → Dom,
          A.transcriptMass z a = ∏ k : Fin t, f k (z (idx₀ k)) := by
        intro z
        unfold LocalAlg.transcriptMass
        simp_rw [h_R, h_idx]
        have h_fk : ∀ k : Fin t,
            f k (z (idx₀ k)) =
              ∏ j : Fin t, (if leaderOf j = k then R₀ j (z (idx₀ k)) (a j) else 1) := by
          intro k
          dsimp [f, M, embed]
          rw [pmfPi_apply]
          refine Finset.prod_congr rfl fun j _ => ?_
          by_cases hjk : leaderOf j = k <;> simp [hjk]
        simp_rw [h_fk]
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Finset.prod_ite_eq, if_pos (Finset.mem_univ (leaderOf j)), h_leader_idx j]
      simp_rw [h_tmass]
      set g : Fin n → Dom → ENNReal := fun i u =>
        ∏ k ∈ Finset.univ.filter (fun k : Fin t => leaderOf k = k ∧ idx₀ k = i), f k u
      have hg_meas : ∀ i, Measurable (g i) := fun i =>
        Finset.measurable_prod _ fun k _ => hf_meas k
      have h_z_eq : ∀ z : Fin n → Dom,
          (∏ k : Fin t, f k (z (idx₀ k))) = ∏ i : Fin n, g i (z i) := by
        intro z
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : Fin t => leaderOf k = k)]
        have h_non : (∏ k ∈ Finset.univ.filter (fun k : Fin t => ¬ leaderOf k = k), f k (z (idx₀ k))) = 1 :=
          Finset.prod_eq_one fun k hk => hf_nonleader k (Finset.mem_filter.mp hk).2 _
        rw [h_non, mul_one,
          ← Finset.prod_fiberwise_of_maps_to (g := idx₀) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.filter_filter]
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [(Finset.mem_filter.mp hk).2.2]
      simp_rw [h_z_eq]
      rw [lintegral_pi_prod_fn P g hg_meas]
      have hg_lint : ∀ i : Fin n,
          (∫⁻ u, g i u ∂P) =
            ∏ k ∈ Finset.univ.filter (fun k : Fin t => leaderOf k = k ∧ idx₀ k = i),
              ∫⁻ u, f k u ∂P := by
        intro i
        apply lintegral_prod_subsingleton P
        intro k₁ hk₁ k₂ hk₂
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
        have hidx_eq : idx₀ k₁ = idx₀ k₂ := hk₁.2.trans hk₂.2.symm
        exact (h_leader_eq_iff k₂ k₁ hk₂.1).mpr hidx_eq |>.symm.trans hk₁.1 |>.symm
      simp_rw [hg_lint]
      change (∏ k : Fin t, ∫⁻ u, f k u ∂P) = _
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : Fin t => leaderOf k = k)]
      have h_non_lint :
          (∏ k ∈ Finset.univ.filter (fun k : Fin t => ¬ leaderOf k = k), ∫⁻ u, f k u ∂P) = 1 := by
        refine Finset.prod_eq_one fun k hk => ?_
        simp [hf_nonleader k (Finset.mem_filter.mp hk).2]
      rw [h_non_lint, mul_one,
        ← Finset.prod_fiberwise_of_maps_to (g := idx₀) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.filter_filter]
    rw [h_prod_lint]
    by_cases hao : A.out a = o <;> simp [hao]
  have h_iid_sum : ∑' o : Out, A.iidOutputLaw P o = 1 := by
    simp_rw [← h_target_eq_iid]
    exact targetMass_tsum u₀ ε M outV P hM_meas hM_loc 0 (fun _ => v₀)
  refine statDiff_le_of_pointwise_ge _ _ β hβ.le hβ1
    (outputLaw_tsum_le_one (simAlg u₀ ε β v₀ M outV) O) h_iid_sum (fun o => ?_)
  rw [← h_target_eq_iid o]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ zero_le)
    (outputLaw_simAlg_ge u₀ ε β v₀ M outV P hε hβ hβ1 ht hM_meas hM_loc O hO o)
  apply ENNReal.ofReal_le_ofReal
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
  have h3φ : 3 * simPhi β t = β / t := by
    unfold simPhi; field_simp
  rw [h3φ]
  have hβt0 : 0 ≤ β / t := by positivity
  have hβt1 : β / t ≤ 1 := by
    rw [div_le_one ht_pos]
    exact hβ1.trans (by exact_mod_cast ht)
  have hbern := bernoulli_sub t (β / t) hβt0 hβt1
  have hmul : (t : ℝ) * (β / t) = β := mul_div_cancel₀ β ht_pos.ne'
  linarith
