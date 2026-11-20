-- Prove2me | solution 1 for UniformDRO.LowerBound.lemma_12_a
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:29:46.067015+00:00
-- url     : https://prove2.me/submissions/5605adfa-2615-4d36-b9b2-036c1c28fcac

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
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hpk : pk k ρ ≤ p) :
    UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id = z₁ := by
  classical
  obtain ⟨hp0, hp1⟩ := hp
  set c := 1 + k * (k - 1) * ρ with hc
  have hc0 : 0 < c := by
    have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
    linarith
  have hpk0 : 0 < pk k ρ := Real.rpow_pos_of_pos hc0 _
  have hppos : 0 < p := lt_of_lt_of_le hpk0 hpk
  unfold UniformDRO.Concentration.robustRisk
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · by_cases hzz : z₀ = z₁
    · -- L ≡ 1
      refine ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₁ p hp0 hp1 _).1,
        ?_, (tp_integral z₀ z₁ p hp0 hp1 _).1, ?_, ?_⟩
      · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2]; ring
      · rw [tp_lintegral]
        simp [UniformDRO.Concentration.cressieRead]
      · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2, hzz]; simp; ring
    · -- all mass on z₁
      set L : ℝ → ℝ := fun x => if x = z₁ then 1 / p else 0 with hL
      have hLm : Measurable L := Measurable.ite (measurableSet_singleton z₁) measurable_const measurable_const
      have hL0 : L z₀ = 0 := by simp [hL, hzz]
      have hL1 : L z₁ = 1 / p := by simp [hL]
      refine ⟨L, hLm, fun x => by simp only [hL]; split_ifs <;> positivity,
        (tp_integral z₀ z₁ p hp0 hp1 _).1, ?_, (tp_integral z₀ z₁ p hp0 hp1 _).1, ?_, ?_⟩
      · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2, hL0, hL1]; field_simp; ring
      · rw [tp_lintegral, hL0, hL1]
        have h0 : UniformDRO.Concentration.cressieRead k 0 = 1 / k := by
          unfold UniformDRO.Concentration.cressieRead
          rw [Real.zero_rpow (by linarith)]
          have : k - 1 ≠ 0 := by linarith
          field_simp; ring
        have hX : p * (1 / p) ^ k ≤ c := by
          have e : p * (1 / p) ^ k = p ^ (1 - k) := by
            rw [one_div, Real.inv_rpow hp0, Real.rpow_sub hppos, Real.rpow_one, div_eq_mul_inv]
          rw [e]
          have hmono : p ^ (1 - k) ≤ (pk k ρ) ^ (1 - k) :=
            Real.rpow_le_rpow_of_nonpos hpk0 hpk (by linarith)
          have hpkpow : (pk k ρ) ^ (1 - k) = c := by
            unfold pk
            rw [← hc, ← Real.rpow_mul hc0.le]
            have : -(1 / (k - 1)) * (1 - k) = 1 := by
              have : k - 1 ≠ 0 := by linarith
              field_simp; ring
            rw [this, Real.rpow_one]
          linarith
        have hk1 : k - 1 ≠ 0 := by linarith
        have hval : (1 - p) * UniformDRO.Concentration.cressieRead k 0
            + p * UniformDRO.Concentration.cressieRead k (1 / p)
            = (p * (1 / p) ^ k - 1) / (k * (k - 1)) := by
          rw [h0]; unfold UniformDRO.Concentration.cressieRead
          field_simp; ring
        have hn0 := cr_nonneg k 0 hk le_rfl
        have hn1 := cr_nonneg k (1 / p) hk (by positivity)
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hp0,
          ← ENNReal.ofReal_add (by positivity) (by positivity), hval]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (by nlinarith)]
        nlinarith
      · rw [(tp_integral z₀ z₁ p hp0 hp1 _).2, hL0, hL1]; field_simp; simp
  · rintro v ⟨L, -, hLnn, -, hL1, -, -, rfl⟩
    rw [(tp_integral z₀ z₁ p hp0 hp1 _).2] at hL1 ⊢
    simp only [id]
    have h1p : 0 ≤ 1 - p := by linarith
    have h := congrArg (fun t => t * z₁) hL1
    nlinarith [mul_nonneg (mul_nonneg h1p (hLnn z₀)) (sub_nonneg.mpr hz)]
