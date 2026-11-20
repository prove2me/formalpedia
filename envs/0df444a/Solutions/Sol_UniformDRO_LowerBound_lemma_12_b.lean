-- Prove2me | solution 1 for UniformDRO.LowerBound.lemma_12_b
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:31:26.217016+00:00
-- url     : https://prove2.me/submissions/f75cfcc2-f45a-4213-a1b6-5d1d4af973ca

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

theorem solution (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hpk : p ≤ pk k ρ) :
    UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id ≤
      UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k) * z₁ + (1 - UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k)) * z₀ := by
  classical
  obtain ⟨hp0, hp1⟩ := hp
  set c := 1 + k * (k - 1) * ρ with hc
  have hc0 : 0 < c := by
    have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
    linarith
  have hk0 : 0 < k := by linarith
  have hk1 : k - 1 ≠ 0 := by linarith
  have hck : UniformDRO.Concentration.ck k ρ = c ^ (1 / k) := rfl
  have hks : 1 / UniformDRO.Concentration.kstar k = 1 - 1 / k := by
    unfold UniformDRO.Concentration.kstar; field_simp
  rw [hck, hks]
  set B := c ^ (1 / k) * p ^ (1 - 1 / k) with hB
  have goal_form : B * z₁ + (1 - B) * z₀ = z₀ + B * (z₁ - z₀) := by ring
  rw [goal_form]
  unfold UniformDRO.Concentration.robustRisk
  apply csSup_le
  · -- L ≡ 1 is feasible
    refine ⟨_, fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₁ p hp0 hp1 _).1,
      ?_, (tp_integral z₀ z₁ p hp0 hp1 _).1, ?_, rfl⟩
    · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2]; ring
    · rw [tp_lintegral]; simp [UniformDRO.Concentration.cressieRead]
  · rintro v ⟨L, -, hLnn, -, hL1, -, hdiv, rfl⟩
    rw [(tp_integral z₀ z₁ p hp0 hp1 _).2] at hL1 ⊢
    simp only [id]
    rw [tp_lintegral] at hdiv
    have hf0 := cr_nonneg k (L z₀) hk (hLnn z₀)
    have hf1 := cr_nonneg k (L z₁) hk (hLnn z₁)
    rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hp0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at hdiv
    have hdivR := (ENNReal.ofReal_le_ofReal_iff hρ.le).mp hdiv
    -- the k-th moment bound: p L₁^k ≤ c
    have hmom : p * L z₁ ^ k ≤ c := by
      unfold UniformDRO.Concentration.cressieRead at hdivR
      have hkk : 0 < k * (k - 1) := by nlinarith
      have e : (1 - p) * ((L z₀ ^ k - k * L z₀ + k - 1) / (k * (k - 1)))
          + p * ((L z₁ ^ k - k * L z₁ + k - 1) / (k * (k - 1)))
          = ((1 - p) * L z₀ ^ k + p * L z₁ ^ k - k * ((1 - p) * L z₀ + p * L z₁) + (k - 1))
            / (k * (k - 1)) := by ring
      rw [e, hL1, div_le_iff₀ hkk] at hdivR
      have : 0 ≤ (1 - p) * L z₀ ^ k := mul_nonneg (by linarith) (Real.rpow_nonneg (hLnn z₀) _)
      nlinarith
    -- hence p L₁ ≤ B
    have hpL : p * L z₁ ≤ B := by
      rcases hp0.eq_or_lt with h0 | hpos
      · subst h0; simp [hB]; positivity
      have hL1le : L z₁ ≤ c ^ (1 / k) * p ^ (-(1 / k)) := by
        have h1 : L z₁ ^ k ≤ c / p := by rw [le_div_iff₀ hpos]; linarith
        have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (hLnn z₁) _) h1 (by positivity : 0 ≤ 1 / k)
        rw [← Real.rpow_mul (hLnn z₁), mul_one_div_cancel hk0.ne', Real.rpow_one,
          Real.div_rpow hc0.le hpos.le, div_eq_mul_inv, ← Real.rpow_neg hpos.le] at h2
        exact h2
      calc p * L z₁ ≤ p * (c ^ (1 / k) * p ^ (-(1 / k))) := by gcongr
        _ = B := by
          rw [hB, mul_left_comm, ← Real.rpow_one_add' hpos.le (by
            have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
            linarith)]
          congr 2
    have hdz : 0 ≤ z₁ - z₀ := sub_nonneg.mpr hz
    have hval : (1 - p) * (L z₀ * z₀) + p * (L z₁ * z₁) = z₀ + p * L z₁ * (z₁ - z₀) := by
      have : (1 - p) * L z₀ = 1 - p * L z₁ := by linarith
      calc (1 - p) * (L z₀ * z₀) + p * (L z₁ * z₁) = ((1 - p) * L z₀) * z₀ + p * L z₁ * z₁ := by ring
        _ = (1 - p * L z₁) * z₀ + p * L z₁ * z₁ := by rw [this]
        _ = _ := by ring
    rw [hval]
    nlinarith [mul_le_mul_of_nonneg_right hpL hdz]
