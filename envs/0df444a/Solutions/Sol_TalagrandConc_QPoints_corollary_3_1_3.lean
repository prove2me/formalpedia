-- Prove2me | solution 1 for TalagrandConc.QPoints.corollary_3_1_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:08:31.693984+00:00
-- url     : https://prove2.me/submissions/89fd1e94-1191-4f4b-baba-a44cc9073a37

import Mathlib



namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- `(q + 1 - q u) u^q ≤ 1` for `0 ≤ u ≤ 1`. -/
lemma key_poly_ineq (q : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((q : ℝ) + 1 - q * u) * u ^ q ≤ 1 := by
  set t := 1 - u with ht
  have hu : u = 1 - t := by rw [ht]; ring
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hb : 1 + (q : ℝ) * t ≤ (1 + t) ^ q := one_add_mul_le_pow (by linarith) q
  have h1 : (q : ℝ) + 1 - q * u = 1 + q * t := by rw [hu]; ring
  rw [h1, hu]
  calc (1 + (q : ℝ) * t) * (1 - t) ^ q ≤ (1 + t) ^ q * (1 - t) ^ q :=
        mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith) q)
    _ = (1 - t ^ 2) ^ q := by rw [← mul_pow]; ring_nf
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

theorem lemma_3_1_2_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) (g : Ω → ℝ) (hg : Measurable g)
    (hlow : ∀ ω, 1 / (q : ℝ) ≤ g ω) (hup : ∀ ω, g ω ≤ 1) :
    (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q ≤ 1 := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hqinv : 0 < 1 / (q : ℝ) := by positivity
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le hqinv (hlow ω)
  have hint_g : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hlow ω, hup ω]
  have hinv_le : ∀ ω, 1 / g ω ≤ q := by
    intro ω
    rw [div_le_iff₀ (hgpos ω)]
    have := hlow ω
    rw [div_le_iff₀ hq0] at this
    linarith
  have hint_inv : Integrable (fun ω => 1 / g ω) μ := by
    refine Integrable.of_bound (hg.inv.aestronglyMeasurable.congr ?_) q
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact Filter.Eventually.of_forall fun ω => by simp
    · rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := hinv_le ω; have : 0 < 1 / g ω := by have := hgpos ω; positivity
        linarith
      · exact hinv_le ω
  have hpt : ∀ ω, 1 / g ω ≤ ((q : ℝ) + 1) - q * g ω := by
    intro ω
    rw [div_le_iff₀ (hgpos ω)]
    have h1 := hlow ω
    rw [div_le_iff₀ hq0] at h1
    have h2 := hup ω
    nlinarith
  have h1 : ∫ ω, 1 / g ω ∂μ ≤ ∫ ω, (((q : ℝ) + 1) - q * g ω) ∂μ := by
    refine integral_mono hint_inv ?_ hpt
    exact (integrable_const _).sub (hint_g.const_mul _)
  have h2 : ∫ ω, (((q : ℝ) + 1) - q * g ω) ∂μ = ((q : ℝ) + 1) - q * ∫ ω, g ω ∂μ := by
    rw [integral_sub (integrable_const _) (hint_g.const_mul _), integral_const,
      integral_const_mul]
    simp
  have hu0 : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg fun ω => (hgpos ω).le
  have hu1 : ∫ ω, g ω ∂μ ≤ 1 := by
    have := integral_mono hint_g (integrable_const (1 : ℝ)) hup
    simpa using this
  have hA : 0 ≤ (∫ ω, g ω ∂μ) ^ q := pow_nonneg hu0 q
  calc (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q
      ≤ (((q : ℝ) + 1) - q * ∫ ω, g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q := by
        rw [← h2]; exact mul_le_mul_of_nonneg_right h1 hA
    _ ≤ 1 := key_poly_ineq q _ hu0 hu1

/-- ENNReal version of Lemma 3.1.2: for measurable `h` with `q⁻¹ ≤ h ≤ 1`. -/
theorem lemma_3_1_2_ennreal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (h : Ω → ℝ≥0∞) (hh : Measurable h)
    (hlow : ∀ ω, (q : ℝ≥0∞)⁻¹ ≤ h ω) (hup : ∀ ω, h ω ≤ 1) :
    (∫⁻ ω, (h ω)⁻¹ ∂μ) * (∫⁻ ω, h ω ∂μ) ^ q ≤ 1 := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hne : ∀ ω, h ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top ENNReal.one_ne_top (hup ω)
  set g : Ω → ℝ := fun ω => (h ω).toReal with hg_def
  have hg : Measurable g := ENNReal.measurable_toReal.comp hh
  have hglow : ∀ ω, 1 / (q : ℝ) ≤ g ω := by
    intro ω
    have := ENNReal.toReal_mono (hne ω) (hlow ω)
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at this
    rw [one_div]; exact this
  have hgup : ∀ ω, g ω ≤ 1 := by
    intro ω
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hup ω)
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le (by positivity) (hglow ω)
  have hreal := lemma_3_1_2_core μ q hq g hg hglow hgup
  have hint_g : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hglow ω, hgup ω, hgpos ω]
  have hinv_le : ∀ ω, 1 / g ω ≤ q := by
    intro ω
    rw [div_le_iff₀ (hgpos ω)]
    have := hglow ω
    rw [div_le_iff₀ hq0] at this
    linarith
  have hint_inv : Integrable (fun ω => 1 / g ω) μ := by
    refine Integrable.of_bound (hg.inv.aestronglyMeasurable.congr ?_) q
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact Filter.Eventually.of_forall fun ω => by simp
    · rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := hinv_le ω; have : 0 < 1 / g ω := by have := hgpos ω; positivity
        linarith
      · exact hinv_le ω
  have e1 : ∫⁻ ω, h ω ∂μ = ENNReal.ofReal (∫ ω, g ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_g (Filter.Eventually.of_forall fun ω => (hgpos ω).le)]
    congr 1
    ext ω
    simp [hg_def, ENNReal.ofReal_toReal (hne ω)]
  have e2 : ∫⁻ ω, (h ω)⁻¹ ∂μ = ENNReal.ofReal (∫ ω, 1 / g ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_inv
      (Filter.Eventually.of_forall fun ω => by have := hgpos ω; positivity)]
    congr 1
    ext ω
    rw [one_div, ENNReal.ofReal_inv_of_pos (hgpos ω)]
    simp [hg_def, ENNReal.ofReal_toReal (hne ω)]
  rw [e1, e2, ← ENNReal.ofReal_pow (integral_nonneg fun ω => (hgpos ω).le),
    ← ENNReal.ofReal_mul (integral_nonneg fun ω => by have := hgpos ω; positivity),
    ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hreal

theorem corollary_3_1_3_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (g : Fin q → Ω → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hup : ∀ i ω, g i ω ≤ 1) :
    (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, g i ω ∂μ ≤ 1 := by
  haveI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  set h : Ω → ℝ≥0∞ := fun ω => max (q : ℝ≥0∞)⁻¹ (⨆ i, g i ω) with hh_def
  have hh : Measurable h := measurable_const.max (Measurable.iSup hg)
  have hlow : ∀ ω, (q : ℝ≥0∞)⁻¹ ≤ h ω := fun ω => le_max_left _ _
  have hq1 : (q : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast (by omega : 1 ≤ q)
  have hup' : ∀ ω, h ω ≤ 1 := fun ω => max_le hq1 (iSup_le fun i => hup i ω)
  have hle : ∀ ω, (⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹) ≤ (h ω)⁻¹ := by
    intro ω
    by_cases hc : (⨆ i, g i ω) ≤ (q : ℝ≥0∞)⁻¹
    · have : h ω = (q : ℝ≥0∞)⁻¹ := max_eq_left hc
      rw [this, inv_inv]
      exact le_trans (iInf_le _ (Classical.arbitrary _)) (min_le_left _ _)
    · push Not at hc
      have : h ω = ⨆ i, g i ω := max_eq_right hc.le
      rw [this]
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => g i ω)
      rw [← hi]
      exact le_trans (iInf_le _ i) (min_le_right _ _)
  have hgh : ∀ i ω, g i ω ≤ h ω := fun i ω => le_trans (le_iSup (fun i => g i ω) i) (le_max_right _ _)
  calc (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, g i ω ∂μ
      ≤ (∫⁻ ω, (h ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, h ω ∂μ := by
        gcongr with i
        · exact hle _
        · exact hgh i _
    _ = (∫⁻ ω, (h ω)⁻¹ ∂μ) * (∫⁻ ω, h ω ∂μ) ^ q := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ 1 := lemma_3_1_2_ennreal μ q hq h hh hlow hup'

/-- Inverse form used in the induction. -/
theorem corollary_3_1_3_inv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (g : Fin q → Ω → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hup : ∀ i ω, g i ω ≤ 1) :
    (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) ≤ (∏ i : Fin q, ∫⁻ ω, g i ω ∂μ)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le]
  exact corollary_3_1_3_core μ q hq g hg hup

end TalagrandConc.QPoints

open TalagrandConc.QPoints
open MeasureTheory
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (g : Fin q → Ω → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hup : ∀ i ω, g i ω ≤ 1) :
    (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, g i ω ∂μ ≤ 1 := by
  exact corollary_3_1_3_core μ q hq g hg hup
