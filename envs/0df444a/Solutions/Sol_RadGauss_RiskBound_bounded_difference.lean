-- Prove2me | solution 1 for RadGauss.RiskBound.bounded_difference
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:16:34.097734+00:00
-- url     : https://prove2.me/submissions/fb0837c6-de10-4232-9bd0-5f96e48f0dbb

import Mathlib
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

set_option autoImplicit false

open MeasureTheory

lemma rg87_abs_iSup_sub_le {ι : Type*} (a b : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b))
    (h : ∀ i, |a i - b i| ≤ c) : |(⨆ i, a i) - ⨆ i, b i| ≤ c := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Real.iSup_of_isEmpty, hc]
  · rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add]
      refine ciSup_le fun j => ?_
      have := (abs_sub_le_iff.1 (h j)).1
      have := le_ciSup hb j
      linarith
    · rw [sub_le_iff_le_add]
      refine ciSup_le fun j => ?_
      have := (abs_sub_le_iff.1 (h j)).2
      have := le_ciSup ha j
      linarith

open RadGauss.RiskBound in
lemma rg87_mem_bound {X Y A : Type*} [Zero A] (φ : Y → A → ℝ)
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1) (F : Set (X → A))
    (h : X × Y → ℝ) (hh : h ∈ phiTildeComp φ F) (z : X × Y) : |h z| ≤ 1 := by
  obtain ⟨f, -, rfl⟩ := hh
  have h1 := hφ01 z.2 (f z.1)
  have h2 := hφ01 z.2 0
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

open RadGauss.RiskBound in
lemma rg87_term_bound {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (z : Fin n → Z) (h : Z → ℝ) (hb : ∀ w, |h w| ≤ 1) :
    (∫ w, h w ∂P) - empMean z h ≤ 2 := by
  have hint : ‖∫ w, h w ∂P‖ ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := h) (C := 1)
      (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hb w)
    simpa using this
  rw [Real.norm_eq_abs, abs_le] at hint
  have hs : -(n : ℝ) ≤ ∑ j, h (z j) := by
    have : ∑ j : Fin n, (-1 : ℝ) ≤ ∑ j, h (z j) :=
      Finset.sum_le_sum fun j _ => (abs_le.1 (hb (z j))).1
    simpa using this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : -1 ≤ empMean z h := by
    unfold empMean
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hnpos]
    linarith
  linarith [hint.2]

open RadGauss.RiskBound in
lemma rg87_emp_diff {Z : Type*} (n : ℕ) (S : Fin n → Z) (i : Fin n) (z' : Z) (h : Z → ℝ)
    (hb : ∀ w, |h w| ≤ 1) :
    |empMean S h - empMean (Function.update S i z') h| ≤ 2 / n := by
  unfold empMean
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hsum : ∑ j, (h (S j) - h (Function.update S i z' j)) = h (S i) - h z' := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  rw [hsum, abs_mul, abs_of_nonneg (by positivity)]
  have : |h (S i) - h z'| ≤ 2 := by
    have := abs_sub (h (S i)) (h z')
    linarith [hb (S i), hb z']
  calc 1 / (n : ℝ) * |h (S i) - h z'| ≤ 1 / (n : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 / n := by ring

open MeasureTheory RadGauss.RiskBound in
theorem solution {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (φ : Y → A → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ)
    (S : Fin n → X × Y) (i : Fin n) (z' : X × Y) :
    |supDev P n (phiTildeComp φ F) S - supDev P n (phiTildeComp φ F) (Function.update S i z')|
      ≤ 2 / n := by
  have hn : 0 < n := Fin.pos i
  have hb : ∀ h : phiTildeComp φ F, ∀ w, |(h : X × Y → ℝ) w| ≤ 1 :=
    fun h w => rg87_mem_bound φ hφ01 F h h.2 w
  unfold supDev
  apply rg87_abs_iSup_sub_le _ _ _ (by positivity)
  · exact ⟨2, by rintro _ ⟨h, rfl⟩; exact rg87_term_bound P n hn S h (hb h)⟩
  · exact ⟨2, by rintro _ ⟨h, rfl⟩; exact rg87_term_bound P n hn _ h (hb h)⟩
  · intro h
    have := rg87_emp_diff n S i z' (h : X × Y → ℝ) (hb h)
    have e : (∫ w, (h : X × Y → ℝ) w ∂P) - empMean S h -
        ((∫ w, (h : X × Y → ℝ) w ∂P) - empMean (Function.update S i z') h) =
        -(empMean S h - empMean (Function.update S i z') h) := by ring
    rw [e, abs_neg]
    exact this
