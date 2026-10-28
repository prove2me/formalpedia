-- Prove2me | solution 1 for PrivLearn.SQSim.iteration_analysis
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:21:10.92557+00:00
-- url     : https://prove2.me/submissions/ec203797-e4f3-4cee-ba75-03270662f1e3

import Mathlib
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_Estimate
open MeasureTheory

namespace Aux_PL59
open PrivLearn.SQSim

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
    · push_neg at hneg
      have : (1 - 3 * t) * (p₁ / p₂) * x₂ ≤ (1 - 3 * t) * (p₁ / p₂) * ((1 + t) * p₂) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e : (1 - 3 * t) * (p₁ / p₂) * ((1 + t) * p₂) = (1 - 3 * t) * (1 + t) * p₁ := by
        field_simp
      nlinarith
  constructor <;> nlinarith [div_pos hp₁ hp₂]

end Aux_PL59

open PrivLearn.SQSim in
theorem solution {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (R : Dom → PMF W) (hmeas : ∀ w, Measurable fun u => R u w)
    (u₀ : Dom) (ε β : ℝ) (t : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t)
    (hR : IsLocalRandomizerPMF R ε) (pt : W → ℝ)
    (hpt : ∀ w, 0 < R u₀ w → |pt w - pTarget P R w| ≤ simPhi β t * pTarget P R w) :
    let φ : ℝ := simPhi β t
    let acc : W → ℝ := fun w => pt w / ((R u₀ w).toReal * (1 + φ) * Real.exp ε)
    let pTerm : ℝ := ∑' w, (R u₀ w).toReal * acc w
    (∀ w, 0 < R u₀ w → 0 ≤ acc w ∧ acc w ≤ 1) ∧
    (1 - φ) / (1 + φ) * Real.exp (-ε) ≤ pTerm ∧ pTerm ≤ Real.exp (-ε) ∧
    ∀ w, |(R u₀ w).toReal * acc w / pTerm - pTarget P R w| ≤ 3 * φ * pTarget P R w := by
  intro φ acc pTerm
  have hφ0 : 0 < φ := by
    show 0 < simPhi β t
    unfold simPhi
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
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
      (fun u => Aux_PL59.loc_real R ε hR u u₀ w)
    simpa [hp, pTarget] using this
  have hp_lo : ∀ w, Real.exp (-ε) * q w ≤ p w := by
    intro w
    have hb : ∀ u, Real.exp (-ε) * q w ≤ (R u w).toReal := by
      intro u
      have h1 := Aux_PL59.loc_real R ε hR u₀ u w
      have h2 : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
      have h3 : Real.exp (-ε) * q w ≤ Real.exp (-ε) * (Real.exp ε * (R u w).toReal) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      rwa [← mul_assoc, h2, one_mul] at h3
    have := integral_mono (integrable_const _) (hint w) hb
    simpa [hp, pTarget] using this
  have hp0 : ∀ w, 0 ≤ p w := fun w =>
    integral_nonneg (fun u => ENNReal.toReal_nonneg)
  -- total mass of the targets
  have hL : ∑' w, (∫⁻ u, R u w ∂P) = 1 := by
    set S : Set W := (R u₀).support with hS
    have hSc : S.Countable := (R u₀).support_countable
    haveI : Countable S := hSc.to_subtype
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
  -- the accepted mass per point
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
    have := (hcb w).1
    calc (1 - φ) / K * p w = (1 - φ) * p w / K := by ring
      _ ≤ q w * acc w := this
  have hhi' : ∀ w, q w * acc w ≤ (1 + φ) / K * p w := by
    intro w
    have := (hcb w).2
    calc q w * acc w ≤ (1 + φ) * p w / K := this
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
  refine ⟨fun w hw => ?_, ?_, ?_, fun w => ?_⟩
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
      have := Aux_PL59.ratio (q w * acc w * K) (pTerm * K) (p w) 1 φ hppos one_pos hφ0.le hφ3
        hx₁ hx₂
      rw [div_one] at this
      have e : q w * acc w * K / (pTerm * K) = q w * acc w / pTerm := by
        rw [mul_div_mul_right _ _ hKpos.ne']
      rw [e] at this
      exact this
