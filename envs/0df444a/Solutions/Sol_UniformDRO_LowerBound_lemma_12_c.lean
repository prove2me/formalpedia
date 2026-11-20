-- Prove2me | solution 1 for UniformDRO.LowerBound.lemma_12_c
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:34:05.966928+00:00
-- url     : https://prove2.me/submissions/80a51faf-7c6a-4911-864c-0b093b3e69c8

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

lemma value_le_z1 (k ρ z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    BddAbove {v : ℝ | ∃ L : ℝ → ℝ, Measurable L ∧ (∀ x, 0 ≤ L x) ∧ Integrable L (twoPointLaw z₀ z₁ p) ∧
      ∫ x, L x ∂(twoPointLaw z₀ z₁ p) = 1 ∧ Integrable (fun x => L x * id x) (twoPointLaw z₀ z₁ p) ∧
      ∫⁻ x, ENNReal.ofReal (UniformDRO.Concentration.cressieRead k (L x)) ∂(twoPointLaw z₀ z₁ p)
        ≤ ENNReal.ofReal ρ ∧
      v = ∫ x, L x * id x ∂(twoPointLaw z₀ z₁ p)} := by
  refine ⟨z₁, ?_⟩
  rintro v ⟨L, -, hLnn, -, hL1, -, -, rfl⟩
  rw [(tp_integral z₀ z₁ p hp0 hp1 _).2] at hL1 ⊢
  simp only [id]
  have h1p : 0 ≤ 1 - p := by linarith
  have h := congrArg (fun t => t * z₁) hL1
  nlinarith [mul_nonneg (mul_nonneg h1p (hLnn z₀)) (sub_nonneg.mpr hz)]

theorem solution (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hp1 : p ≤ pk k ρ)
    (hp2 : p ≤ 1 - (1 - β) ^ (1 - UniformDRO.Concentration.kstar k) * pk k ρ) :
    β ^ (1 / k) * UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k) * z₁ +
        (1 - β ^ (1 / k) * UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k)) * z₀ ≤
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id := by
  classical
  obtain ⟨hp0, hp1'⟩ := hp
  obtain ⟨hβ0, hβ1⟩ := hβ
  set c := 1 + k * (k - 1) * ρ with hc
  have hc0 : 0 < c := by
    have : 0 < k * (k - 1) * ρ := mul_pos (mul_pos (by linarith) (by linarith)) hρ
    linarith
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hck : UniformDRO.Concentration.ck k ρ = c ^ (1 / k) := rfl
  have hks : 1 / UniformDRO.Concentration.kstar k = 1 - 1 / k := by
    unfold UniformDRO.Concentration.kstar; field_simp
  have hks2 : 1 - UniformDRO.Concentration.kstar k = -(1 / (k - 1)) := by
    unfold UniformDRO.Concentration.kstar; field_simp; ring
  have hpk : pk k ρ = c ^ (-(1 / (k - 1))) := rfl
  rw [hck, hks]
  rw [hks2, hpk] at hp2
  rw [hpk] at hp1
  set A := β ^ (1 / k) * c ^ (1 / k) * p ^ (1 - 1 / k) with hA
  have goal_form : A * z₁ + (1 - A) * z₀ = z₀ + A * (z₁ - z₀) := by ring
  rw [goal_form]
  unfold UniformDRO.Concentration.robustRisk
  rcases hp0.eq_or_lt with h0 | hpos
  · -- p = 0: the trivial ratio
    subst h0
    have hA0 : A = 0 := by
      rw [hA, Real.zero_rpow (by
        have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
        linarith), mul_zero]
    rw [hA0, zero_mul, add_zero]
    refine le_csSup (value_le_z1 k ρ z₀ z₁ 0 hz le_rfl (by norm_num))
      ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₁ 0 le_rfl (by norm_num) _).1,
        ?_, (tp_integral z₀ z₁ 0 le_rfl (by norm_num) _).1, ?_, ?_⟩
    · rw [(tp_integral z₀ z₁ 0 le_rfl (by norm_num) _).2]; ring
    · rw [tp_lintegral]; simp [UniformDRO.Concentration.cressieRead]
    · rw [(tp_integral z₀ z₁ 0 le_rfl (by norm_num) _).2]; simp
  -- p > 0
  have hq0 : 0 < (1 - β) ^ (-(1 / (k - 1))) * c ^ (-(1 / (k - 1))) := by positivity
  have hp_lt1 : p < 1 := by linarith
  have h1p : 0 < 1 - p := by linarith
  set L1 := β ^ (1 / k) * c ^ (1 / k) * p ^ (-(1 / k)) with hL1def
  have hpL1 : p * L1 = A := by
    rw [hL1def, hA]
    have : p * p ^ (-(1 / k)) = p ^ (1 - 1 / k) := by
      rw [← Real.rpow_one_add' hpos.le (by
        have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
        linarith)]; congr 1
    rw [← this]; ring
  -- p L1 < 1
  have hA1 : A ≤ β ^ (1 / k) := by
    have hpp : p ^ (1 - 1 / k) ≤ (c ^ (-(1 / (k - 1)))) ^ (1 - 1 / k) :=
      Real.rpow_le_rpow hpos.le hp1 (by
        have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
        linarith)
    have hpow : (c ^ (-(1 / (k - 1)))) ^ (1 - 1 / k) = c ^ (-(1 / k)) := by
      rw [← Real.rpow_mul hc0.le]; congr 1; field_simp
    rw [hpow] at hpp
    calc A = β ^ (1 / k) * (c ^ (1 / k) * p ^ (1 - 1 / k)) := by rw [hA]; ring
      _ ≤ β ^ (1 / k) * (c ^ (1 / k) * c ^ (-(1 / k))) := by gcongr
      _ = β ^ (1 / k) := by rw [← Real.rpow_add hc0]; simp
  have hβk : β ^ (1 / k) < 1 := Real.rpow_lt_one hβ0.le hβ1 (by positivity)
  set L0 := (1 - A) / (1 - p) with hL0def
  have hL0nn : 0 ≤ L0 := div_nonneg (by linarith) h1p.le
  have hL1nn : 0 ≤ L1 := by positivity
  set L : ℝ → ℝ := fun x => if x = z₁ then L1 else L0 with hL
  by_cases hzz : z₀ = z₁
  · -- degenerate support: every feasible value equals z₀ = z₁
    subst hzz
    have hv : z₀ + A * (z₀ - z₀) = ∫ x, (fun _ => (1 : ℝ)) x * id x ∂(twoPointLaw z₀ z₀ p) := by
      rw [(tp_integral z₀ z₀ p hp0 hp1' _).2]; simp; ring
    rw [hv]
    refine le_csSup (value_le_z1 k ρ z₀ z₀ p le_rfl hp0 hp1')
      ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, (tp_integral z₀ z₀ p hp0 hp1' _).1,
        ?_, (tp_integral z₀ z₀ p hp0 hp1' _).1, ?_, rfl⟩
    · rw [(tp_integral z₀ z₀ p hp0 hp1' _).2]; ring
    · rw [tp_lintegral]; simp [UniformDRO.Concentration.cressieRead]
  have hLz0 : L z₀ = L0 := by simp [hL, hzz]
  have hLz1 : L z₁ = L1 := by simp [hL]
  have hLm : Measurable L := Measurable.ite (measurableSet_singleton z₁) measurable_const measurable_const
  have hLnn : ∀ x, 0 ≤ L x := fun x => by simp only [hL]; split_ifs <;> assumption
  refine le_of_eq_of_le ?_ (le_csSup (value_le_z1 k ρ z₀ z₁ p hz hp0 hp1')
    ⟨L, hLm, hLnn, (tp_integral z₀ z₁ p hp0 hp1' _).1, ?_, (tp_integral z₀ z₁ p hp0 hp1' _).1, ?_, rfl⟩)
  · rw [(tp_integral z₀ z₁ p hp0 hp1' _).2, hLz0, hLz1]; simp only [id]
    have e0 : (1 - p) * L0 = 1 - A := by rw [hL0def]; field_simp
    calc z₀ + A * (z₁ - z₀) = (1 - A) * z₀ + A * z₁ := by ring
      _ = ((1 - p) * L0) * z₀ + (p * L1) * z₁ := by rw [e0, hpL1]
      _ = _ := by ring
  · rw [(tp_integral z₀ z₁ p hp0 hp1' _).2, hLz0, hLz1]
    have e0 : (1 - p) * L0 = 1 - A := by rw [hL0def]; field_simp
    linarith [hpL1]
  · -- divergence constraint
    rw [tp_lintegral, hLz0, hLz1]
    have hf0 := cr_nonneg k L0 hk hL0nn
    have hf1 := cr_nonneg k L1 hk hL1nn
    rw [← ENNReal.ofReal_mul h1p.le, ← ENNReal.ofReal_mul hp0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold UniformDRO.Concentration.cressieRead
    have hkk : 0 < k * (k - 1) := by nlinarith
    -- p L1^k = β c
    have hpL1k : p * L1 ^ k = β * c := by
      rw [hL1def, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hβ0.le, ← Real.rpow_mul hc0.le, ← Real.rpow_mul hpos.le]
      have e1 : 1 / k * k = 1 := by field_simp
      have e2 : -(1 / k) * k = -1 := by field_simp
      rw [e1, e2, Real.rpow_one, Real.rpow_one, Real.rpow_neg_one]
      field_simp
    -- (1 - p) L0^k ≤ (1 - β) c
    have hL0le : L0 ≤ 1 / (1 - p) := by
      rw [hL0def]; exact div_le_div_of_nonneg_right (by nlinarith [show 0 ≤ A by positivity]) h1p.le
    have hL0k : (1 - p) * L0 ^ k ≤ (1 - β) * c := by
      have h1 : L0 ^ k ≤ (1 / (1 - p)) ^ k := Real.rpow_le_rpow hL0nn hL0le hk0.le
      have h2 : (1 - p) * (1 / (1 - p)) ^ k = (1 - p) ^ (1 - k) := by
        rw [one_div, Real.inv_rpow h1p.le, Real.rpow_sub h1p, Real.rpow_one, div_eq_mul_inv]
      have h3 : (1 - p) ^ (1 - k) ≤ (1 - β) * c := by
        -- from hp2: 1 - p ≥ ((1-β) c)^(-1/(k-1))
        have hq : ((1 - β) * c) ^ (-(1 / (k - 1))) ≤ 1 - p := by
          rw [Real.mul_rpow (by linarith) hc0.le]; linarith
        have hqpos : 0 < ((1 - β) * c) ^ (-(1 / (k - 1))) := by
          have : 0 < (1 - β) * c := mul_pos (by linarith) hc0
          positivity
        have := Real.rpow_le_rpow_of_nonpos hqpos hq (by linarith : 1 - k ≤ 0)
        rw [← Real.rpow_mul (by have : 0 < (1 - β) * c := mul_pos (by linarith) hc0; linarith)] at this
        have e : -(1 / (k - 1)) * (1 - k) = 1 := by field_simp; ring
        rw [e, Real.rpow_one] at this
        exact this
      calc (1 - p) * L0 ^ k ≤ (1 - p) * (1 / (1 - p)) ^ k := by gcongr
        _ = (1 - p) ^ (1 - k) := h2
        _ ≤ _ := h3
    have e0 : (1 - p) * L0 = 1 - A := by rw [hL0def]; field_simp
    have hEL : (1 - p) * L0 + p * L1 = 1 := by linarith [hpL1]
    clear_value L L0 L1 A
    have e : (1 - p) * ((L0 ^ k - k * L0 + k - 1) / (k * (k - 1)))
        + p * ((L1 ^ k - k * L1 + k - 1) / (k * (k - 1)))
        = ((1 - p) * L0 ^ k + p * L1 ^ k - k * ((1 - p) * L0 + p * L1) + (k - 1)) / (k * (k - 1)) := by
      ring
    rw [e, hEL, hpL1k, div_le_iff₀ hkk]
    have hcc : c - 1 = k * (k - 1) * ρ := by rw [hc]; ring
    linarith [hL0k, hcc]
