-- Prove2me | solution 1 for PalmQueueing.Loynes.ergodic_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:49:51.048156+00:00
-- url     : https://prove2.me/submissions/5e69e505-5a8d-4462-ba18-c20031465dc4

import Mathlib

/-!
# Lemma 2.2.1: the ergodic lemma behind Loynes' theorem (§2.2.3, p.87)
-/


namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For a bounded truncation `Z ∧ C` the integral of `Z ∧ C − (Z ∧ C) ∘ θ` vanishes by invariance. -/
lemma integral_trunc_sub_eq_zero (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω → Ω) (hshift : Measurable shift) (hinv : Measure.map shift P0 = P0)
    (Z : Ω → ℝ) (hZmeas : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω) (C : ℝ) :
    ∫ ω, (min (Z ω) C - min (Z (shift ω)) C) ∂P0 = 0 := by
  have hmeas : Measurable (fun ω => min (Z ω) C) := hZmeas.min measurable_const
  have hbdd : ∀ ω, ‖min (Z ω) C‖ ≤ |C| := by
    intro ω
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rcases le_or_gt (Z ω) C with h | h
      · rw [min_eq_left h]
        have := hZ0 ω
        linarith [neg_abs_le C, abs_nonneg C]
      · rw [min_eq_right h.le]
        linarith [neg_abs_le C]
    · exact (min_le_right _ _).trans (le_abs_self C)
  have hint1 : Integrable (fun ω => min (Z ω) C) P0 :=
    Integrable.of_bound hmeas.aestronglyMeasurable |C| (Filter.Eventually.of_forall hbdd)
  have hint2 : Integrable (fun ω => min (Z (shift ω)) C) P0 := by
    have : Integrable (fun ω => min (Z ω) C) (Measure.map shift P0) := by rwa [hinv]
    exact (integrable_map_measure hmeas.aestronglyMeasurable hshift.aemeasurable).1 this
  rw [integral_sub hint1 hint2]
  have : ∫ ω, min (Z (shift ω)) C ∂P0 = ∫ ω, min (Z ω) C ∂P0 := by
    conv_rhs => rw [← hinv]
    rw [integral_map hshift.aemeasurable hmeas.aestronglyMeasurable]
  rw [this, sub_self]

theorem ergodic_lemma_core (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω → Ω) (hshift : Measurable shift) (hinv : Measure.map shift P0 = P0)
    (Z : Ω → ℝ) (hZmeas : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hint : Integrable (fun ω => Z ω - Z (shift ω)) P0) :
    ∫ ω, (Z ω - Z (shift ω)) ∂P0 = 0 := by
  set F : ℕ → Ω → ℝ := fun n ω => min (Z ω) (n : ℝ) - min (Z (shift ω)) (n : ℝ) with hF
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) P0 := by
    intro n
    exact ((hZmeas.min measurable_const).sub
      ((hZmeas.comp hshift).min measurable_const)).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ ω ∂P0, ‖F n ω‖ ≤ |Z ω - Z (shift ω)| := by
    intro n
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [hF, Real.norm_eq_abs]
    rw [abs_le]
    have h := abs_le.1 (le_refl |Z ω - Z (shift ω)|)
    constructor
    · rcases le_or_gt (Z ω) n with h1 | h1 <;> rcases le_or_gt (Z (shift ω)) n with h2 | h2
      · rw [min_eq_left h1, min_eq_left h2]; linarith [neg_abs_le (Z ω - Z (shift ω))]
      · rw [min_eq_left h1, min_eq_right h2.le]; linarith [neg_abs_le (Z ω - Z (shift ω)), abs_nonneg (Z ω - Z (shift ω))]
      · rw [min_eq_right h1.le, min_eq_left h2]; linarith [neg_abs_le (Z ω - Z (shift ω)), le_abs_self (Z ω - Z (shift ω))]
      · rw [min_eq_right h1.le, min_eq_right h2.le]; linarith [abs_nonneg (Z ω - Z (shift ω))]
    · rcases le_or_gt (Z ω) n with h1 | h1 <;> rcases le_or_gt (Z (shift ω)) n with h2 | h2
      · rw [min_eq_left h1, min_eq_left h2]; linarith [le_abs_self (Z ω - Z (shift ω))]
      · rw [min_eq_left h1, min_eq_right h2.le]; linarith [le_abs_self (Z ω - Z (shift ω))]
      · rw [min_eq_right h1.le, min_eq_left h2]; linarith [abs_nonneg (Z ω - Z (shift ω))]
      · rw [min_eq_right h1.le, min_eq_right h2.le]; linarith [abs_nonneg (Z ω - Z (shift ω))]
  have hlim : ∀ᵐ ω ∂P0, Tendsto (fun n => F n ω) atTop (𝓝 (Z ω - Z (shift ω))) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    apply tendsto_const_nhds.congr'
    rw [EventuallyEq, eventually_atTop]
    refine ⟨⌈max (Z ω) (Z (shift ω))⌉₊, fun n hn => ?_⟩
    have h1 : Z ω ≤ n := by
      have := Nat.le_ceil (max (Z ω) (Z (shift ω)))
      have h2 : ((⌈max (Z ω) (Z (shift ω))⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      linarith [le_max_left (Z ω) (Z (shift ω))]
    have h2 : Z (shift ω) ≤ n := by
      have := Nat.le_ceil (max (Z ω) (Z (shift ω)))
      have h2 : ((⌈max (Z ω) (Z (shift ω))⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      linarith [le_max_right (Z ω) (Z (shift ω))]
    simp only [hF, min_eq_left h1, min_eq_left h2]
  have hconv := tendsto_integral_of_dominated_convergence (fun ω => |Z ω - Z (shift ω)|)
    hFmeas hint.abs hbound hlim
  have hzero : ∀ n, ∫ ω, F n ω ∂P0 = 0 := fun n =>
    integral_trunc_sub_eq_zero P0 shift hshift hinv Z hZmeas hZ0 (n : ℝ)
  simp only [hzero] at hconv
  exact (tendsto_nhds_unique hconv tendsto_const_nhds)

end PalmQueueing.Loynes

open PalmQueueing.Loynes
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω → Ω) (hshift : Measurable shift) (hinv : Measure.map shift P0 = P0)
    (Z : Ω → ℝ) (hZmeas : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hint : Integrable (fun ω => Z ω - Z (shift ω)) P0) :
    ∫ ω, (Z ω - Z (shift ω)) ∂P0 = 0 := by
  exact ergodic_lemma_core P0 shift hshift hinv Z hZmeas hZ0 hint
