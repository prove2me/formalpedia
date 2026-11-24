-- Prove2me | solution 1 for ThinShellSampling.eq_1_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:45:54.986416+00:00
-- url     : https://prove2.me/submissions/84793bbb-7e91-49bc-a3b1-b8f4729ece45

import Mathlib
import Definitions.Def_ThinShellSampling_renyi

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace SolTSSEq13

/-- `(ab)^q = b · (a^q b^{q-1})` for finite `b` and `q > 1`. -/
lemma pt1 (a b : ℝ≥0∞) (hb : b ≠ ⊤) (q : ℝ) (hq : 1 < q) :
    (a * b) ^ q = b * (a ^ q * b ^ (q - 1)) := by
  by_cases hb0 : b = 0
  · rw [hb0, mul_zero, zero_mul, ENNReal.zero_rpow_of_pos (by linarith)]
  · rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
    have : b ^ q = b * b ^ (q - 1) := by
      conv_lhs => rw [show q = 1 + (q - 1) by ring]
      rw [ENNReal.rpow_add _ _ hb0 hb, ENNReal.rpow_one]
    rw [this]; ring

/-- `b · b^e = b^{1+e}` for finite `b` and `e > 0`. -/
lemma pt2 (b : ℝ≥0∞) (hb : b ≠ ⊤) (e : ℝ) (he : 0 < e) : b * b ^ e = b ^ (1 + e) := by
  by_cases hb0 : b = 0
  · rw [hb0, zero_mul, ENNReal.zero_rpow_of_pos (by linarith)]
  · rw [ENNReal.rpow_add _ _ hb0 hb, ENNReal.rpow_one]

end SolTSSEq13

open SolTSSEq13 in
theorem solution {α : Type*} [MeasurableSpace α] (q l : ℝ) (hq : 1 < q) (hl0 : 0 < l) (hl1 : l < 1)
    (μ ν π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] :
    ThinShellSampling.renyi q μ π ≤
      ENNReal.ofReal ((q - l) / (q - 1)) * ThinShellSampling.renyi (q / l) μ ν +
        ThinShellSampling.renyi ((q - l) / (1 - l)) ν π := by
  have hq1 : q ≠ 1 := ne_of_gt hq
  have h1l : 0 < 1 - l := by linarith
  have hs1 : 1 < q / l := by rw [lt_div_iff₀ hl0]; linarith
  have hs2 : 1 < (q - l) / (1 - l) := by rw [lt_div_iff₀ h1l]; linarith
  have hcoef : 0 < (q - l) / (q - 1) := div_pos (by linarith) (by linarith)
  -- trivial cases where the right-hand side is infinite
  by_cases hμν : μ ≪ ν
  swap
  · have : ThinShellSampling.renyi (q / l) μ ν = ⊤ := by
      unfold ThinShellSampling.renyi
      rw [if_neg (fun h => hμν h.2.2)]
    rw [this, ENNReal.mul_top (by simpa using hcoef), top_add]
    exact le_top
  by_cases hνπ : ν ≪ π
  swap
  · have : ThinShellSampling.renyi ((q - l) / (1 - l)) ν π = ⊤ := by
      unfold ThinShellSampling.renyi
      rw [if_neg (fun h => hνπ h.2.2)]
    rw [this, add_top]
    exact le_top
  set f := μ.rnDeriv ν with hf_def
  set g := ν.rnDeriv π with hg_def
  set I1 := ∫⁻ x, f x ^ (q / l) ∂ν with hI1_def
  set I2 := ∫⁻ x, g x ^ ((q - l) / (1 - l)) ∂π with hI2_def
  have hc1 : IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧ μ ≪ ν :=
    ⟨inferInstance, inferInstance, hμν⟩
  have hc2 : IsProbabilityMeasure ν ∧ IsProbabilityMeasure π ∧ ν ≪ π :=
    ⟨inferInstance, inferInstance, hνπ⟩
  have hμπ : μ ≪ π := hμν.trans hνπ
  have hc0 : IsProbabilityMeasure μ ∧ IsProbabilityMeasure π ∧ μ ≪ π :=
    ⟨inferInstance, inferInstance, hμπ⟩
  by_cases hI1 : I1 = ⊤
  · have : ThinShellSampling.renyi (q / l) μ ν = ⊤ := by
      unfold ThinShellSampling.renyi
      simp only [if_pos hc1, if_neg (ne_of_gt hs1)]
      rw [if_pos hI1]
    rw [this, ENNReal.mul_top (by simpa using hcoef), top_add]
    exact le_top
  by_cases hI2 : I2 = ⊤
  · have : ThinShellSampling.renyi ((q - l) / (1 - l)) ν π = ⊤ := by
      unfold ThinShellSampling.renyi
      simp only [if_pos hc2, if_neg (ne_of_gt hs2)]
      rw [if_pos hI2]
    rw [this, add_top]
    exact le_top
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  have hgm : Measurable g := Measure.measurable_rnDeriv _ _
  have hgfin : ∀ᵐ x ∂π, g x ≠ ⊤ := (Measure.rnDeriv_lt_top ν π).mono fun x hx => hx.ne
  have hgfinν : ∀ᵐ x ∂ν, g x ≠ ⊤ := hνπ.ae_le hgfin
  have hν_eq : π.withDensity g = ν := Measure.withDensity_rnDeriv_eq ν π hνπ
  -- change of measure from `ν` to `π`
  have hchange : ∀ F : α → ℝ≥0∞, Measurable F → ∫⁻ x, F x ∂ν = ∫⁻ x, g x * F x ∂π := by
    intro F hF
    conv_lhs => rw [← hν_eq]
    rw [lintegral_withDensity_eq_lintegral_mul _ hgm hF]
    rfl
  set I := ∫⁻ x, (μ.rnDeriv π x) ^ q ∂π with hI_def
  -- Step 1: `I = ∫ f^q g^{q-1} dν`
  have hIeq : I = ∫⁻ x, f x ^ q * g x ^ (q - 1) ∂ν := by
    rw [hchange (fun x => f x ^ q * g x ^ (q - 1)) ((hfm.pow_const q).mul (hgm.pow_const (q - 1)))]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := π) hμν, hgfin] with x hx hxg
    rw [← hx, Pi.mul_apply]
    exact pt1 (f x) (g x) hxg q hq
  -- Step 2: Hölder
  have hpq : (l⁻¹).HolderConjugate ((1 - l)⁻¹) :=
    Real.HolderConjugate.inv_inv hl0 h1l (by ring)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq
    ((hfm.pow_const q).aemeasurable) ((hgm.pow_const (q - 1)).aemeasurable)
  have hA : ∫⁻ x, (f x ^ q) ^ l⁻¹ ∂ν = I1 := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_mul, div_eq_mul_inv]
  have hB : ∫⁻ x, (g x ^ (q - 1)) ^ (1 - l)⁻¹ ∂ν = I2 := by
    rw [hchange (fun x => (g x ^ (q - 1)) ^ (1 - l)⁻¹) ((hgm.pow_const (q - 1)).pow_const _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hgfin] with x hxg
    rw [← ENNReal.rpow_mul, pt2 _ hxg _ (by
      have : 0 < q - 1 := by linarith
      positivity)]
    congr 1
    field_simp
    ring
  rw [hA, hB, one_div, inv_inv, one_div, inv_inv] at hH
  simp only [Pi.mul_apply] at hH
  rw [← hIeq] at hH
  -- hH : I ≤ I1 ^ l * I2 ^ (1 - l)
  have hRHSfin : I1 ^ l * I2 ^ (1 - l) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hl0.le hI1)
      (ENNReal.rpow_ne_top_of_nonneg h1l.le hI2)
  have hIfin : I ≠ ⊤ := ne_top_of_le_ne_top hRHSfin hH
  -- unfold the divergences
  have hr0 : ThinShellSampling.renyi q μ π = ENNReal.ofReal (Real.log I.toReal / (q - 1)) := by
    unfold ThinShellSampling.renyi
    simp only [if_pos hc0, if_neg hq1]
    rw [if_neg hIfin]
  have hr1 : ThinShellSampling.renyi (q / l) μ ν =
      ENNReal.ofReal (Real.log I1.toReal / (q / l - 1)) := by
    unfold ThinShellSampling.renyi
    simp only [if_pos hc1, if_neg (ne_of_gt hs1)]
    rw [if_neg hI1]
  have hr2 : ThinShellSampling.renyi ((q - l) / (1 - l)) ν π =
      ENNReal.ofReal (Real.log I2.toReal / ((q - l) / (1 - l) - 1)) := by
    unfold ThinShellSampling.renyi
    simp only [if_pos hc2, if_neg (ne_of_gt hs2)]
    rw [if_neg hI2]
  rw [hr0, hr1, hr2]
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := I)) with h0 | hpos
  · rw [← h0, Real.log_zero, zero_div, ENNReal.ofReal_zero]
    exact zero_le
  have hreal : I.toReal ≤ I1.toReal ^ l * I2.toReal ^ (1 - l) := by
    have := ENNReal.toReal_mono hRHSfin hH
    rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at this
  have hI1pos : 0 < I1.toReal := by
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := I1)) with h | h
    · rw [← h, Real.zero_rpow hl0.ne', zero_mul] at hreal; linarith
    · exact h
  have hI2pos : 0 < I2.toReal := by
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := I2)) with h | h
    · rw [← h, Real.zero_rpow h1l.ne', mul_zero] at hreal; linarith
    · exact h
  have hlog : Real.log I.toReal ≤ l * Real.log I1.toReal + (1 - l) * Real.log I2.toReal := by
    have := Real.log_le_log hpos hreal
    rwa [Real.log_mul (Real.rpow_pos_of_pos hI1pos l).ne' (Real.rpow_pos_of_pos hI2pos _).ne',
      Real.log_rpow hI1pos, Real.log_rpow hI2pos] at this
  have hq1' : 0 < q - 1 := by linarith
  have e1 : (q - l) / (q - 1) * (Real.log I1.toReal / (q / l - 1)) =
      l * Real.log I1.toReal / (q - 1) := by
    have : q / l - 1 = (q - l) / l := by field_simp
    rw [this]
    have hql : q - l ≠ 0 := by linarith
    field_simp
  have e2 : Real.log I2.toReal / ((q - l) / (1 - l) - 1) =
      (1 - l) * Real.log I2.toReal / (q - 1) := by
    have : (q - l) / (1 - l) - 1 = (q - 1) / (1 - l) := by field_simp; ring
    rw [this]
    field_simp
  rw [← ENNReal.ofReal_mul hcoef.le, e1, e2]
  refine le_trans ?_ ENNReal.ofReal_add_le
  apply ENNReal.ofReal_le_ofReal
  rw [← add_div]
  exact div_le_div_of_nonneg_right hlog hq1'.le
