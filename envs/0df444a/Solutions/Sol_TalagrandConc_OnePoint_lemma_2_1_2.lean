-- Prove2me | solution 1 for TalagrandConc.OnePoint.lemma_2_1_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:46:06.081573+00:00
-- url     : https://prove2.me/submissions/ef390946-67ea-4f38-84f1-dcccc50b3a5a

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal


namespace TalagrandConc.OnePoint

/-- Pointwise bound: `min(e^t, 1/g) + e^t g ≤ 1 + e^t` for `g ∈ [0,1]`. -/
lemma min_inv_add_le (t : ℝ) (g : ℝ≥0∞) (hg : g ≤ 1) :
    min (ENNReal.ofReal (Real.exp t)) g⁻¹ + ENNReal.ofReal (Real.exp t) * g
      ≤ 1 + ENNReal.ofReal (Real.exp t) := by
  set E := Real.exp t with hE
  have hE0 : 0 < E := Real.exp_pos t
  rcases eq_or_ne g 0 with h0 | h0
  · subst h0
    simp
  have hgt : g ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hg
  set r := g.toReal with hr
  have hgr : g = ENNReal.ofReal r := (ENNReal.ofReal_toReal hgt).symm
  have hr0 : 0 < r := ENNReal.toReal_pos h0 hgt
  have hr1 : r ≤ 1 := by
    rw [hgr] at hg
    exact (ENNReal.ofReal_le_one).1 hg
  rw [hgr, ← ENNReal.ofReal_inv_of_pos hr0, ← ENNReal.ofReal_mul hE0.le,
    show (1 : ℝ≥0∞) + ENNReal.ofReal E = ENNReal.ofReal (1 + E) by
      rw [ENNReal.ofReal_add zero_le_one hE0.le, ENNReal.ofReal_one]]
  rcases le_or_gt (E * r) 1 with h | h
  · calc min (ENNReal.ofReal E) (ENNReal.ofReal r⁻¹) + ENNReal.ofReal (E * r)
        ≤ ENNReal.ofReal E + ENNReal.ofReal (E * r) := add_le_add (min_le_left _ _) le_rfl
      _ = ENNReal.ofReal (E + E * r) := by rw [ENNReal.ofReal_add hE0.le (by positivity)]
      _ ≤ ENNReal.ofReal (1 + E) := ENNReal.ofReal_le_ofReal (by linarith)
  · calc min (ENNReal.ofReal E) (ENNReal.ofReal r⁻¹) + ENNReal.ofReal (E * r)
        ≤ ENNReal.ofReal r⁻¹ + ENNReal.ofReal (E * r) := add_le_add (min_le_right _ _) le_rfl
      _ = ENNReal.ofReal (r⁻¹ + E * r) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (1 + E) := by
          apply ENNReal.ofReal_le_ofReal
          have : r⁻¹ ≤ 1 + E - E * r := by
            rw [inv_eq_one_div, div_le_iff₀ hr0]
            nlinarith [mul_le_mul_of_nonneg_right h.le (sub_nonneg.2 hr1)]
          linarith

/-- The real quadratic bound `(1 + E - E u) u ≤ a(t)` with `E = e^t`. -/
lemma quad_le_aOne (t u : ℝ) :
    (1 + Real.exp t - Real.exp t * u) * u ≤ aOne t := by
  unfold aOne
  have hE0 : 0 < Real.exp t := Real.exp_pos t
  rw [Real.exp_neg]
  have key : aOne t - (1 + Real.exp t - Real.exp t * u) * u
      = (1 + Real.exp t - 2 * Real.exp t * u) ^ 2 / (4 * Real.exp t) := by
    unfold aOne
    rw [Real.exp_neg]
    field_simp
    ring
  have : 0 ≤ (1 + Real.exp t - 2 * Real.exp t * u) ^ 2 / (4 * Real.exp t) := by positivity
  unfold aOne at key
  rw [Real.exp_neg] at key
  linarith

/-- ENNReal-valued core of Lemma 2.1.2. -/
theorem lemma_2_1_2_ennreal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ≥0∞) (hg : Measurable g) (hg1 : ∀ ω, g ω ≤ 1) (t : ℝ) :
    (∫⁻ ω, min (ENNReal.ofReal (Real.exp t)) (g ω)⁻¹ ∂μ) * (∫⁻ ω, g ω ∂μ)
      ≤ ENNReal.ofReal (aOne t) := by
  set E := ENNReal.ofReal (Real.exp t) with hE
  set Y := ∫⁻ ω, min E (g ω)⁻¹ ∂μ with hY
  set u := ∫⁻ ω, g ω ∂μ with hu
  have hmeas : Measurable fun ω => min E (g ω)⁻¹ := measurable_const.min hg.inv
  have hsum : Y + E * u ≤ 1 + E := by
    rw [hY, hu, ← lintegral_const_mul E hg, ← lintegral_add_left hmeas]
    calc ∫⁻ ω, (min E (g ω)⁻¹ + E * g ω) ∂μ ≤ ∫⁻ _, (1 + E) ∂μ :=
          lintegral_mono fun ω => min_inv_add_le t (g ω) (hg1 ω)
      _ = 1 + E := by rw [lintegral_const, measure_univ, mul_one]
  have hu1 : u ≤ 1 := by
    rw [hu]
    calc ∫⁻ ω, g ω ∂μ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono hg1
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
  have hYt : Y ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hEt⟩) ?_
    exact le_trans le_self_add hsum
  have hut : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  set y := Y.toReal with hy
  set ur := u.toReal with hur
  have hY' : Y = ENNReal.ofReal y := (ENNReal.ofReal_toReal hYt).symm
  have hu' : u = ENNReal.ofReal ur := (ENNReal.ofReal_toReal hut).symm
  have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
  have hur0 : 0 ≤ ur := ENNReal.toReal_nonneg
  have hur1 : ur ≤ 1 := by
    rw [hu'] at hu1
    exact ENNReal.ofReal_le_one.1 hu1
  have hE0 : 0 < Real.exp t := Real.exp_pos t
  have hsum' : y + Real.exp t * ur ≤ 1 + Real.exp t := by
    rw [hY', hu', hE, ← ENNReal.ofReal_mul hE0.le, ← ENNReal.ofReal_add hy0 (by positivity),
      show (1 : ℝ≥0∞) + ENNReal.ofReal (Real.exp t) = ENNReal.ofReal (1 + Real.exp t) by
        rw [ENNReal.ofReal_add zero_le_one hE0.le, ENNReal.ofReal_one]] at hsum
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsum
  rw [hY', hu', ← ENNReal.ofReal_mul hy0]
  apply ENNReal.ofReal_le_ofReal
  calc y * ur ≤ (1 + Real.exp t - Real.exp t * ur) * ur := by
        apply mul_le_mul_of_nonneg_right _ hur0
        linarith
    _ ≤ aOne t := quad_le_aOne t ur

theorem lemma_2_1_2_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) (t : ℝ) :
    (∫⁻ ω, min (ENNReal.ofReal (Real.exp t)) (ENNReal.ofReal (g ω))⁻¹ ∂μ) *
        (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal (aOne t) := by
  exact lemma_2_1_2_ennreal μ (fun ω => ENNReal.ofReal (g ω)) hg.ennreal_ofReal
    (fun ω => ENNReal.ofReal_le_one.2 (hg1 ω)) t

end TalagrandConc.OnePoint

open TalagrandConc.OnePoint


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) (t : ℝ) :
    (∫⁻ ω, min (ENNReal.ofReal (Real.exp t)) (ENNReal.ofReal (g ω))⁻¹ ∂μ) *
        (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal (aOne t) := by
  exact lemma_2_1_2_core μ g hg hg0 hg1 t
