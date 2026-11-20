-- Prove2me | solution 1 for UniformDRO.LowerBound.primal_two_point
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:36:19.695235+00:00
-- url     : https://prove2.me/submissions/f29b9345-930e-4dea-bd10-8d7bee26a40b

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

open MeasureTheory UniformDRO.LowerBound

lemma tp_integral (z₀ z₁ p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : ℝ → ℝ) :
    Integrable g (twoPointLaw z₀ z₁ p) ∧
    ∫ x, g x ∂(twoPointLaw z₀ z₁ p) = (1 - p) * g z₀ + p * g z₁ := by
  have i0 : Integrable g (Measure.dirac z₀) := integrable_dirac (by simp)
  have i1 : Integrable g (Measure.dirac z₁) := integrable_dirac (by simp)
  refine ⟨(i0.smul_measure ENNReal.ofReal_ne_top).add_measure (i1.smul_measure ENNReal.ofReal_ne_top), ?_⟩
  rw [twoPointLaw, integral_add_measure (i0.smul_measure ENNReal.ofReal_ne_top)
    (i1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hp0]
  simp [smul_eq_mul]

lemma tp_lintegral (z₀ z₁ p : ℝ) (g : ℝ → ENNReal) :
    ∫⁻ x, g x ∂(twoPointLaw z₀ z₁ p) = ENNReal.ofReal (1 - p) * g z₀ + ENNReal.ofReal p * g z₁ := by
  rw [twoPointLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  simp [smul_eq_mul]


lemma cr_nonneg (k t : ℝ) (hk : 1 < k) (ht : 0 ≤ t) : 0 ≤ UniformDRO.Concentration.cressieRead k t := by
  unfold UniformDRO.Concentration.cressieRead
  apply div_nonneg _ (by nlinarith)
  have := one_add_mul_self_le_rpow_one_add (show (-1 : ℝ) ≤ t - 1 by linarith) hk.le
  rw [show 1 + (t - 1) = t by ring] at this
  linarith

/-- the constraint after the change of variables `L₀ = (1-q)/(1-p)`, `L₁ = q/p` -/
lemma cons_eq (k p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - p) * ((1 - q) / (1 - p)) ^ k + p * (q / p) ^ k
      = (1 - p) ^ (1 - k) * (1 - q) ^ k + p ^ (1 - k) * q ^ k := by
  have h1p : 0 < 1 - p := by linarith
  rw [Real.div_rpow (by linarith) h1p.le, Real.div_rpow hq0 hp0.le, Real.rpow_sub h1p, Real.rpow_sub hp0,
    Real.rpow_one, Real.rpow_one]
  field_simp

lemma div_form (k L0 L1 p : ℝ) (hk : 1 < k) (hE : (1 - p) * L0 + p * L1 = 1) :
    (1 - p) * UniformDRO.Concentration.cressieRead k L0 + p * UniformDRO.Concentration.cressieRead k L1
      = ((1 - p) * L0 ^ k + p * L1 ^ k - 1) / (k * (k - 1)) := by
  unfold UniformDRO.Concentration.cressieRead
  have e : (1 - p) * ((L0 ^ k - k * L0 + k - 1) / (k * (k - 1)))
      + p * ((L1 ^ k - k * L1 + k - 1) / (k * (k - 1)))
      = ((1 - p) * L0 ^ k + p * L1 ^ k - k * ((1 - p) * L0 + p * L1) + (k - 1)) / (k * (k - 1)) := by
    ring
  rw [e, hE]; ring

theorem solution (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id =
      z₀ + (z₁ - z₀) * sSup {q ∈ Set.Icc (0 : ℝ) 1 |
        (1 - p) ^ (1 - k) * (1 - q) ^ k + p ^ (1 - k) * q ^ k ≤ UniformDRO.Concentration.ck k ρ ^ k} := by
  classical
  obtain ⟨hp0, hp1⟩ := hp
  have h1p : 0 < 1 - p := by linarith
  set c := 1 + k * (k - 1) * ρ with hc
  have hc0 : 0 < c := by
    have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
    linarith
  have hk0 : 0 < k := by linarith
  have hkk : 0 < k * (k - 1) := by nlinarith
  have hcc : c - 1 = k * (k - 1) * ρ := by rw [hc]; ring
  have hC : UniformDRO.Concentration.ck k ρ ^ k = c := by
    show (c ^ (1 / k)) ^ k = c
    rw [← Real.rpow_mul hc0.le, one_div_mul_cancel hk0.ne', Real.rpow_one]
  rw [hC]
  set Q := {q ∈ Set.Icc (0 : ℝ) 1 | (1 - p) ^ (1 - k) * (1 - q) ^ k + p ^ (1 - k) * q ^ k ≤ c} with hQ
  set g : ℝ → ℝ := fun q => z₀ + (z₁ - z₀) * q with hg
  have hpQ : p ∈ Q := by
    refine ⟨⟨hp0.le, hp1.le⟩, ?_⟩
    have e : (1 - p) ^ (1 - k) * (1 - p) ^ k + p ^ (1 - k) * p ^ k = 1 := by
      rw [← Real.rpow_add h1p, ← Real.rpow_add hp0]; simp
    rw [e]; nlinarith [hcc, mul_pos hkk hρ]
  have hQbdd : BddAbove Q := ⟨1, fun q hq => hq.1.2⟩
  have hgm : Monotone g := fun a b hab => by
    simp only [hg]; nlinarith [sub_nonneg.mpr hz]
  have hgc : ContinuousAt g (sSup Q) := by
    simp only [hg]; fun_prop
  unfold UniformDRO.Concentration.robustRisk
  show _ = g (sSup Q)
  rw [hgm.map_csSup_of_continuousAt hgc ⟨p, hpQ⟩ hQbdd]
  congr 1
  ext v
  constructor
  · rintro ⟨L, -, hLnn, -, hL1, -, hdiv, rfl⟩
    rw [(tp_integral z₀ z₁ p hp0.le hp1.le _).2] at hL1
    rw [(tp_integral z₀ z₁ p hp0.le hp1.le _).2]
    simp only [id]
    refine ⟨p * L z₁, ⟨⟨by have := hLnn z₁; positivity, by nlinarith [hLnn z₀]⟩, ?_⟩, ?_⟩
    · rw [tp_lintegral] at hdiv
      have hf0 := cr_nonneg k (L z₀) hk (hLnn z₀)
      have hf1 := cr_nonneg k (L z₁) hk (hLnn z₁)
      rw [← ENNReal.ofReal_mul h1p.le, ← ENNReal.ofReal_mul hp0.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)] at hdiv
      have hdivR := (ENNReal.ofReal_le_ofReal_iff hρ.le).mp hdiv
      rw [div_form k (L z₀) (L z₁) p hk hL1, div_le_iff₀ hkk] at hdivR
      have hq0 : 0 ≤ p * L z₁ := by have := hLnn z₁; positivity
      have hq1 : p * L z₁ ≤ 1 := by nlinarith [hLnn z₀]
      rw [← cons_eq k p (p * L z₁) hp0 hp1 hq0 hq1]
      have e0 : (1 - p * L z₁) / (1 - p) = L z₀ := by
        rw [div_eq_iff h1p.ne']; linarith
      have e1 : p * L z₁ / p = L z₁ := by field_simp
      rw [e0, e1]
      linarith [hcc]
    · simp only [hg]
      have : (1 - p) * L z₀ = 1 - p * L z₁ := by linarith
      calc z₀ + (z₁ - z₀) * (p * L z₁) = (1 - p * L z₁) * z₀ + p * L z₁ * z₁ := by ring
        _ = ((1 - p) * L z₀) * z₀ + p * L z₁ * z₁ := by rw [this]
        _ = _ := by ring
  · rintro ⟨q, ⟨⟨hq0, hq1⟩, hcons⟩, rfl⟩
    by_cases hzz : z₀ = z₁
    · subst hzz
      refine ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₀ p hp0.le hp1.le _).1,
        ?_, (tp_integral z₀ z₀ p hp0.le hp1.le _).1, ?_, ?_⟩
      · rw [(tp_integral z₀ z₀ p hp0.le hp1.le _).2]; ring
      · rw [tp_lintegral]; simp [UniformDRO.Concentration.cressieRead]
      · rw [(tp_integral z₀ z₀ p hp0.le hp1.le _).2]; simp [hg]; ring
    set L : ℝ → ℝ := fun x => if x = z₁ then q / p else (1 - q) / (1 - p) with hL
    have hLz0 : L z₀ = (1 - q) / (1 - p) := by simp [hL, hzz]
    have hLz1 : L z₁ = q / p := by simp [hL]
    have hLnn : ∀ x, 0 ≤ L x := fun x => by
      simp only [hL]; split_ifs
      · exact div_nonneg hq0 hp0.le
      · exact div_nonneg (by linarith) h1p.le
    have hE : (1 - p) * L z₀ + p * L z₁ = 1 := by rw [hLz0, hLz1]; field_simp; ring
    refine ⟨L, Measurable.ite (measurableSet_singleton z₁) measurable_const measurable_const, hLnn,
      (tp_integral z₀ z₁ p hp0.le hp1.le _).1, ?_, (tp_integral z₀ z₁ p hp0.le hp1.le _).1, ?_, ?_⟩
    · rw [(tp_integral z₀ z₁ p hp0.le hp1.le _).2]; exact hE
    · rw [tp_lintegral]
      have hf0 := cr_nonneg k (L z₀) hk (hLnn z₀)
      have hf1 := cr_nonneg k (L z₁) hk (hLnn z₁)
      rw [← ENNReal.ofReal_mul h1p.le, ← ENNReal.ofReal_mul hp0.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity), div_form k (L z₀) (L z₁) p hk hE]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hkk, hLz0, hLz1, cons_eq k p q hp0 hp1 hq0 hq1]
      linarith [hcc]
    · rw [(tp_integral z₀ z₁ p hp0.le hp1.le _).2, hLz0, hLz1]; simp only [hg, id]
      field_simp; ring
