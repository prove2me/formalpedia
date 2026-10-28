-- Prove2me | solution 1 for PrivLearn.SQSim.claim_5_10_estimate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:15:12.120851+00:00
-- url     : https://prove2.me/submissions/9da7fd47-eba1-49fe-82a3-a54c173a2dd7

import Mathlib
import Definitions.Def_PrivLearn_SQSim_Privacy
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_Estimate
open MeasureTheory

namespace Aux_PL510
open PrivLearn.SQSim

lemma loc_real {Dom W : Type*} (R : Dom → PMF W) (e : ℝ) (h : IsLocalRandomizerPMF R e)
    (u u' : Dom) (w : W) : (R u w).toReal ≤ Real.exp e * (R u' w).toReal := by
  have h1 := h u u' w
  have hne : ENNReal.ofReal (Real.exp e) * R u' w ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)
  have := ENNReal.toReal_mono hne h1
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos e).le] at this

lemma eps_nonneg {Dom W : Type*} (R : Dom → PMF W) (e : ℝ) (h : IsLocalRandomizerPMF R e)
    (u : Dom) : 0 ≤ e := by
  obtain ⟨w, hw⟩ := (R u).support_nonempty
  have hpos : 0 < (R u w).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hw) (PMF.apply_ne_top _ _)
  have := loc_real R e h u u w
  have h1 : 1 ≤ Real.exp e := by
    by_contra hc; push_neg at hc; nlinarith
  by_contra hc; push_neg at hc
  have := Real.exp_lt_one_iff.mpr hc
  linarith

lemma prod_bound {Dom W : Type*} {m : ℕ} (Rs : Fin m → Dom → PMF W) (es : Fin m → ℝ)
    (hloc : ∀ j, IsLocalRandomizerPMF (Rs j) (es j)) (a : Fin m → W) (u u' : Dom) :
    ∏ j, (Rs j u (a j)).toReal ≤ Real.exp (∑ j, es j) * ∏ j, (Rs j u' (a j)).toReal := by
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun j _ => ENNReal.toReal_nonneg)
    (fun j _ => loc_real (Rs j) (es j) (hloc j) u u' (a j))

lemma estimate {Dom : Type*} [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
    (r : Dom → ℝ) (hr : Measurable r) (u₀ : Dom) (ε : ℝ) (hε : 0 < ε) (hr0 : 0 < r u₀)
    (hlo : ∀ u, Real.exp (-ε) * r u₀ ≤ r u) (hhi : ∀ u, r u ≤ Real.exp ε * r u₀)
    (τ : ℝ) (hτ : 0 < τ) (v : ℝ) (hv : IsSQAnswer P (sqQuery r u₀ ε) τ v) :
    (∀ u, sqQuery r u₀ ε u ∈ Set.Icc (-1 : ℝ) 1) ∧
      |sqEstimate r u₀ ε v - ∫ u, r u ∂P| ≤ Real.exp (2 * ε) * τ * ∫ u, r u ∂P ∧
      0 < ∫ u, r u ∂P := by
  have hD : 0 < Real.exp ε - Real.exp (-ε) := by
    have := Real.exp_lt_exp.mpr (show -ε < ε by linarith); linarith
  have he1 : 1 ≤ Real.exp ε := Real.one_le_exp hε.le
  have he2 : Real.exp (-ε) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have he3 : 0 < Real.exp (-ε) := Real.exp_pos _
  have hden : 0 < r u₀ * (Real.exp ε - Real.exp (-ε)) := mul_pos hr0 hD
  have hint : Integrable r P := by
    refine Integrable.of_bound hr.aestronglyMeasurable (Real.exp ε * r u₀)
      (Filter.Eventually.of_forall (fun u => ?_))
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := hlo u; nlinarith
    · exact hhi u
  have hp_lo : Real.exp (-ε) * r u₀ ≤ ∫ u, r u ∂P := by
    have := integral_mono (integrable_const (Real.exp (-ε) * r u₀)) hint hlo
    simpa using this
  have hp_pos : 0 < ∫ u, r u ∂P := lt_of_lt_of_le (by positivity) hp_lo
  refine ⟨fun u => ?_, ?_, hp_pos⟩
  · unfold sqQuery
    rw [Set.mem_Icc, le_div_iff₀ hden, div_le_iff₀ hden]
    have a1 := hlo u
    have a2 := hhi u
    constructor <;> nlinarith
  · have hq : ∫ u, sqQuery r u₀ ε u ∂P = (∫ u, r u ∂P - r u₀) / (r u₀ * (Real.exp ε - Real.exp (-ε))) := by
      unfold sqQuery
      rw [integral_div, integral_sub hint (integrable_const _), integral_const, probReal_univ,
        one_smul]
    unfold IsSQAnswer at hv
    rw [hq] at hv
    have hest : sqEstimate r u₀ ε v - ∫ u, r u ∂P =
        (r u₀ * (Real.exp ε - Real.exp (-ε))) *
          (v - (∫ u, r u ∂P - r u₀) / (r u₀ * (Real.exp ε - Real.exp (-ε)))) := by
      unfold sqEstimate
      field_simp
      ring
    rw [hest, abs_mul, abs_of_pos hden]
    have h1 : r u₀ * (Real.exp ε - Real.exp (-ε)) *
        |v - (∫ u, r u ∂P - r u₀) / (r u₀ * (Real.exp ε - Real.exp (-ε)))| ≤
        r u₀ * (Real.exp ε - Real.exp (-ε)) * τ := mul_le_mul_of_nonneg_left hv hden.le
    have h2 : r u₀ ≤ Real.exp ε * ∫ u, r u ∂P := by
      have : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have h3 : Real.exp (2 * ε) = Real.exp ε * Real.exp ε := by rw [← Real.exp_add]; ring_nf
    rw [h3]
    have h4 : Real.exp ε - Real.exp (-ε) ≤ Real.exp ε := by linarith
    calc r u₀ * (Real.exp ε - Real.exp (-ε)) *
          |v - (∫ u, r u ∂P - r u₀) / (r u₀ * (Real.exp ε - Real.exp (-ε)))|
        ≤ r u₀ * (Real.exp ε - Real.exp (-ε)) * τ := h1
      _ ≤ (Real.exp ε * ∫ u, r u ∂P) * Real.exp ε * τ := by
          apply mul_le_mul_of_nonneg_right _ hτ.le
          exact mul_le_mul h2 h4 hD.le (by positivity)
      _ = Real.exp ε * Real.exp ε * τ * ∫ u, r u ∂P := by ring

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

end Aux_PL510

open PrivLearn.SQSim in
theorem solution {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (m : ℕ) (Rs : Fin m → Dom → PMF W) (es : Fin m → ℝ)
    (Rk : Dom → PMF W) (ek : ℝ)
    (hmeas_s : ∀ j w, Measurable fun u => Rs j u w) (hmeas_k : ∀ w, Measurable fun u => Rk u w)
    (hloc_s : ∀ j, IsLocalRandomizerPMF (Rs j) (es j)) (hloc_k : IsLocalRandomizerPMF Rk ek)
    (ε : ℝ) (hε : 0 < ε) (hbudget : ∑ j, es j + ek ≤ ε)
    (a : Fin m → W) (w : W) (u₀ : Dom)
    (hpos : 0 < (Rk u₀ w).toReal * ∏ j, (Rs j u₀ (a j)).toReal)
    (τ : ℝ) (hτ : 0 < τ) (v₁ v₂ : ℝ) :
    let r₁ : Dom → ℝ := fun u => (Rk u w).toReal * ∏ j, (Rs j u (a j)).toReal
    let r₂ : Dom → ℝ := fun u => ∏ j, (Rs j u (a j)).toReal
    let p₁ : ℝ := ∫ u, r₁ u ∂P
    let p₂ : ℝ := ∫ u, r₂ u ∂P
    let τ' : ℝ := Real.exp (2 * ε) * τ
    IsSQAnswer P (sqQuery r₁ u₀ ε) τ v₁ → IsSQAnswer P (sqQuery r₂ u₀ ε) τ v₂ →
    (∀ u, sqQuery r₁ u₀ ε u ∈ Set.Icc (-1 : ℝ) 1 ∧ sqQuery r₂ u₀ ε u ∈ Set.Icc (-1 : ℝ) 1) ∧
    |sqEstimate r₁ u₀ ε v₁ - p₁| ≤ τ' * p₁ ∧ |sqEstimate r₂ u₀ ε v₂ - p₂| ≤ τ' * p₂ ∧
    (τ' ≤ 1 / 3 →
      |sqEstimate r₁ u₀ ε v₁ / sqEstimate r₂ u₀ ε v₂ - p₁ / p₂| ≤ 3 * τ' * (p₁ / p₂)) := by
  intro r₁ r₂ p₁ p₂ τ' hv₁ hv₂
  have hek : 0 ≤ ek := Aux_PL510.eps_nonneg Rk ek hloc_k u₀
  have hes : 0 ≤ ∑ j, es j := Finset.sum_nonneg (fun j _ => Aux_PL510.eps_nonneg _ _ (hloc_s j) u₀)
  have hS₂ : ∑ j, es j ≤ ε := by linarith
  have hr₂0 : 0 < r₂ u₀ := by
    have hk : 0 ≤ (Rk u₀ w).toReal := ENNReal.toReal_nonneg
    have : 0 ≤ r₂ u₀ := Finset.prod_nonneg (fun j _ => ENNReal.toReal_nonneg)
    rcases this.lt_or_eq with h | h
    · exact h
    · exfalso; simp only [r₂] at h; rw [← h, mul_zero] at hpos; exact lt_irrefl _ hpos
  have hr₂nn : ∀ u, 0 ≤ r₂ u := fun u => Finset.prod_nonneg (fun j _ => ENNReal.toReal_nonneg)
  -- ratio bounds
  have hb₂ : ∀ u u', r₂ u ≤ Real.exp ε * r₂ u' := by
    intro u u'
    refine le_trans (Aux_PL510.prod_bound Rs es hloc_s a u u') ?_
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hS₂) (hr₂nn u')
  have hb₁ : ∀ u u', r₁ u ≤ Real.exp ε * r₁ u' := by
    intro u u'
    have h1 := Aux_PL510.loc_real Rk ek hloc_k u u' w
    have h2 := Aux_PL510.prod_bound Rs es hloc_s a u u'
    have h3 : r₁ u ≤ Real.exp ek * (Rk u' w).toReal * (Real.exp (∑ j, es j) * r₂ u') :=
      mul_le_mul h1 h2 (hr₂nn u) (by positivity)
    have h4 : Real.exp ek * Real.exp (∑ j, es j) ≤ Real.exp ε := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    calc r₁ u ≤ Real.exp ek * (Rk u' w).toReal * (Real.exp (∑ j, es j) * r₂ u') := h3
      _ = (Real.exp ek * Real.exp (∑ j, es j)) * r₁ u' := by simp only [r₁, r₂]; ring
      _ ≤ Real.exp ε * r₁ u' := mul_le_mul_of_nonneg_right h4
          (mul_nonneg ENNReal.toReal_nonneg (hr₂nn u'))
  have hlo : ∀ (r : Dom → ℝ), (∀ u u', r u ≤ Real.exp ε * r u') →
      ∀ u, Real.exp (-ε) * r u₀ ≤ r u := by
    intro r hb u
    have := hb u₀ u
    have h1 : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (-ε) * r u₀ ≤ Real.exp (-ε) * (Real.exp ε * r u) :=
      mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    rw [← mul_assoc, h1, one_mul] at h2
    exact h2
  have hm₂ : Measurable r₂ :=
    Finset.measurable_prod _ (fun j _ => (hmeas_s j (a j)).ennreal_toReal)
  have hm₁ : Measurable r₁ := (hmeas_k w).ennreal_toReal.mul hm₂
  obtain ⟨q₁, e₁, pp₁⟩ := Aux_PL510.estimate P r₁ hm₁ u₀ ε hε hpos (hlo r₁ hb₁)
    (fun u => hb₁ u u₀) τ hτ v₁ hv₁
  obtain ⟨q₂, e₂, pp₂⟩ := Aux_PL510.estimate P r₂ hm₂ u₀ ε hε hr₂0 (hlo r₂ hb₂)
    (fun u => hb₂ u u₀) τ hτ v₂ hv₂
  refine ⟨fun u => ⟨q₁ u, q₂ u⟩, e₁, e₂, fun ht => ?_⟩
  exact Aux_PL510.ratio _ _ _ _ τ' pp₁ pp₂ (by positivity) ht e₁ e₂
