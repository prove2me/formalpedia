-- Prove2me | solution 1 for SampleDrivenOS.Linear.b9_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:53:50.193952+00:00
-- url     : https://prove2.me/submissions/1af67465-0878-486a-a165-dca41cf5348f

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

set_option autoImplicit false
open SampleDrivenOS.Linear

lemma ib_phi_eq (c : ℝ) : (fun y : ℝ => y * (1 - c * Real.log y)) = fun y => y - c * (y * Real.log y) := by
  funext y; ring

lemma ib_phi_cont (c : ℝ) : Continuous fun y : ℝ => y * (1 - c * Real.log y) := by
  rw [ib_phi_eq]
  exact continuous_id.sub (continuous_const.mul Real.continuous_mul_log)

lemma ib_phi_cont1 : Continuous fun y : ℝ => y * (1 - Real.log y) := by
  have := ib_phi_cont 1
  simpa using this

/-- `y log y ≥ -1/e`. -/
lemma ib_mul_log_ge (y : ℝ) (hy : 0 ≤ y) : -(1 / Real.exp 1) ≤ y * Real.log y := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp; positivity
  · have he : 0 < Real.exp 1 := Real.exp_pos 1
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (y * Real.exp 1) by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul h.ne' he.ne', Real.log_one,
      Real.log_exp] at h1
    have h2 : 1 / (y * Real.exp 1) * y = 1 / Real.exp 1 := by field_simp
    nlinarith

lemma ib_phi_nonneg (c : ℝ) (hc : 0 ≤ c) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ y * (1 - c * Real.log y) := by
  have : Real.log y ≤ 0 := Real.log_nonpos hy0 hy1
  have : 0 ≤ 1 - c * Real.log y := by nlinarith
  positivity

/-- `y ↦ y (1 - log y)` is monotone on `[0,1]`. -/
lemma ib_phi_mono : MonotoneOn (fun y : ℝ => y * (1 - Real.log y)) (Set.Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ib_phi_cont1.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := hx.1.ne'
    exact ((differentiableAt_id.mul ((differentiableAt_const _).sub
      (Real.differentiableAt_log hx0)))).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hd : HasDerivAt (fun y : ℝ => y * (1 - Real.log y)) (1 * (1 - Real.log x) + x * (0 - x⁻¹)) x :=
      (hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_log hx0))
    rw [hd.deriv]
    have : x * (0 - x⁻¹) = -1 := by rw [zero_sub, mul_neg, mul_inv_cancel₀ hx0]
    rw [this]
    have : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
    linarith

theorem solution (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 / p * (∫ y in (0 : ℝ)..1, 1 / (1 / (p * s) - 1 + y * (1 - p * Real.log y))) ≤
      1 / p - (1 - p) / p * ((1 / (p * s) - 1 / Real.exp 1) *
        Real.log ((1 / (p * s) + p / Real.exp 1) / (1 / (p * s) + p / Real.exp 1 - 1))) := by
  obtain ⟨hs0, hs1, hint⟩ := hs
  obtain ⟨hp0, hp1⟩ := hp
  set X : ℝ := 1 / (p * s) with hX
  set E : ℝ := 1 / Real.exp 1 with hE
  have hE0 : 0 < E := by positivity
  have hE1 : E < 1 := by
    rw [hE, div_lt_one (Real.exp_pos 1)]
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  have hX1 : 1 < X := by
    rw [hX, lt_div_iff₀ (by positivity)]
    nlinarith
  have hcs : 0 < 1 / s - 1 := by
    have : 1 < 1 / s := by rw [lt_div_iff₀ hs0]; linarith
    linarith
  have hXs : X - 1 / s = (1 - p) * X := by rw [hX]; field_simp
  set A : ℝ → ℝ := fun y => y * (1 - Real.log y) + 1 / s - 1 with hA
  set H : ℝ → ℝ := fun y => X - 1 + y * (1 - p * Real.log y) with hH
  set w : ℝ → ℝ := fun y => 1 / A y with hw
  set K : ℝ := X - 1 + p * E with hK
  have hK0 : 0 < K := by have : 0 < p * E := by positivity
                         linarith
  set g : ℝ → ℝ := fun y => (X - E) / (K + y) with hg
  -- positivity facts on `[0,1]`
  have hApos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < A y := by
    intro y hy
    have := ib_phi_nonneg 1 zero_le_one y hy.1 hy.2
    simp only [one_mul] at this
    simp only [hA]; linarith
  have hHpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < H y := by
    intro y hy
    have := ib_phi_nonneg p hp0.le y hy.1 hy.2
    simp only [hH]; linarith
  -- pointwise bound
  have hpt : ∀ y ∈ Set.Icc (0 : ℝ) 1, 1 / H y ≤ w y - (1 - p) * (w y * g y) := by
    intro y hy
    have ha := hApos y hy
    have hh := hHpos y hy
    set N : ℝ := X + y * Real.log y with hN
    have hHA : H y = A y + (1 - p) * N := by
      simp only [hH, hA, hN]; linear_combination hXs
    have hNge : X - E ≤ N := by have := ib_mul_log_ge y hy.1; simp only [hN]; linarith
    have hHle : H y ≤ K + y := by
      have h1 := ib_mul_log_ge y hy.1
      simp only [hH, hK]
      nlinarith
    have hiden : 1 / H y = 1 / A y - (1 - p) * (N / (A y * H y)) := by
      field_simp
      rw [hHA]; ring
    have hgN : g y ≤ N / H y := by
      simp only [hg]
      rw [div_le_div_iff₀ (by linarith) hh]
      have : 0 ≤ X - E := by linarith
      nlinarith
    have : w y * g y ≤ N / (A y * H y) := by
      simp only [hw]
      rw [show N / (A y * H y) = 1 / A y * (N / H y) by field_simp]
      exact mul_le_mul_of_nonneg_left hgN (by positivity)
    rw [hiden]
    simp only [hw] at this ⊢
    have : 0 ≤ 1 - p := by linarith
    nlinarith
  -- continuity / integrability
  have hAc : ContinuousOn A (Set.uIcc 0 1) :=
    ((ib_phi_cont1.add continuous_const).sub continuous_const).continuousOn
  have hHc : ContinuousOn H (Set.uIcc 0 1) :=
    (continuous_const.add (ib_phi_cont p)).continuousOn
  rw [Set.uIcc_of_le zero_le_one] at hAc hHc
  have hwc : ContinuousOn w (Set.Icc 0 1) :=
    continuousOn_const.div hAc (fun y hy => (hApos y hy).ne')
  have hgc : ContinuousOn g (Set.Icc 0 1) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun y hy => by have := hy.1; simp; linarith)
  have hHic : ContinuousOn (fun y => 1 / H y) (Set.Icc 0 1) :=
    continuousOn_const.div hHc (fun y hy => (hHpos y hy).ne')
  have iI : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) → IntervalIntegrable f MeasureTheory.volume 0 1 := by
    intro f hf
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le zero_le_one]
  have hw1 : ∫ y in (0 : ℝ)..1, w y = 1 := hint
  -- Chebyshev: ∫ w g ≥ ∫ g
  have hwanti : AntitoneOn w (Set.Icc 0 1) := by
    intro x hx y hy hxy
    have h1 := ib_phi_mono hx hy hxy
    simp only [hw]
    apply one_div_le_one_div_of_le (hApos x hx)
    simp only [hA]; linarith
  have hganti : AntitoneOn g (Set.Icc 0 1) := by
    intro x hx y hy hxy
    simp only [hg]
    apply div_le_div_of_nonneg_left (by linarith) (by linarith [hx.1]) (by linarith)
  obtain ⟨y0, hy0, hy0prop⟩ : ∃ y0 ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (w y - 1) * (g y - g y0) := by
    by_cases hc1 : 1 ≤ w 1
    · refine ⟨1, ⟨zero_le_one, le_refl 1⟩, fun y hy => ?_⟩
      have h1 : w 1 ≤ w y := hwanti hy ⟨zero_le_one, le_refl 1⟩ hy.2
      have h2 : g 1 ≤ g y := hganti hy ⟨zero_le_one, le_refl 1⟩ hy.2
      exact mul_nonneg (by linarith) (by linarith)
    by_cases hc0 : w 0 ≤ 1
    · refine ⟨0, ⟨le_refl 0, zero_le_one⟩, fun y hy => ?_⟩
      have h1 : w y ≤ w 0 := hwanti ⟨le_refl 0, zero_le_one⟩ hy hy.1
      have h2 : g y ≤ g 0 := hganti ⟨le_refl 0, zero_le_one⟩ hy hy.1
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    push_neg at hc1 hc0
    obtain ⟨y0, hy0, hwy0⟩ := intermediate_value_Icc' zero_le_one hwc ⟨hc1.le, hc0.le⟩
    refine ⟨y0, hy0, fun y hy => ?_⟩
    rcases le_total y y0 with h | h
    · have h1 : w y0 ≤ w y := hwanti hy hy0 h
      have h2 : g y0 ≤ g y := hganti hy hy0 h
      exact mul_nonneg (by linarith) (by linarith)
    · have h1 : w y ≤ w y0 := hwanti hy0 hy h
      have h2 : g y ≤ g y0 := hganti hy0 hy h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hcheb : ∫ y in (0 : ℝ)..1, g y ≤ ∫ y in (0 : ℝ)..1, w y * g y := by
    have hmono : ∫ y in (0 : ℝ)..1, (g y + g y0 * w y - g y0) ≤ ∫ y in (0 : ℝ)..1, w y * g y := by
      apply intervalIntegral.integral_mono_on zero_le_one
      · exact iI _ ((hgc.add (continuousOn_const.mul hwc)).sub continuousOn_const)
      · exact iI _ (hwc.mul hgc)
      · intro y hy
        have := hy0prop y hy
        nlinarith
    have hcalc : ∫ y in (0 : ℝ)..1, (g y + g y0 * w y - g y0) = ∫ y in (0 : ℝ)..1, g y := by
      have i1 : IntervalIntegrable (fun y => g y + g y0 * w y) MeasureTheory.volume 0 1 :=
        iI _ (hgc.add (continuousOn_const.mul hwc))
      have i2 : IntervalIntegrable (fun y => g y0 * w y) MeasureTheory.volume 0 1 :=
        iI _ (continuousOn_const.mul hwc)
      have e1 := intervalIntegral.integral_sub i1 (intervalIntegrable_const (c := g y0))
      have e2 := intervalIntegral.integral_add (iI _ hgc) i2
      have e3 : ∫ y in (0 : ℝ)..1, g y0 * w y = g y0 * ∫ y in (0 : ℝ)..1, w y :=
        intervalIntegral.integral_const_mul _ _
      rw [e1, e2, e3, hw1]
      simp
    linarith
  -- main integral comparison
  have hmain : ∫ y in (0 : ℝ)..1, 1 / H y ≤ 1 - (1 - p) * ∫ y in (0 : ℝ)..1, w y * g y := by
    have := intervalIntegral.integral_mono_on zero_le_one (iI _ hHic)
      (iI (fun y => w y - (1 - p) * (w y * g y)) (hwc.sub (continuousOn_const.mul (hwc.mul hgc)))) hpt
    have i2 : IntervalIntegrable (fun y => (1 - p) * (w y * g y)) MeasureTheory.volume 0 1 :=
      iI _ (continuousOn_const.mul (hwc.mul hgc))
    have e1 := intervalIntegral.integral_sub (iI _ hwc) i2
    have e2 : ∫ y in (0 : ℝ)..1, (1 - p) * (w y * g y) = (1 - p) * ∫ y in (0 : ℝ)..1, w y * g y :=
      intervalIntegral.integral_const_mul _ _
    rw [e1, e2, hw1] at this
    exact this
  -- the explicit integral of `g`
  have hgint : ∫ y in (0 : ℝ)..1, g y = (X - E) * Real.log ((X + p / Real.exp 1) / (X + p / Real.exp 1 - 1)) := by
    have hfun : g = fun y => (X - E) * (1 / (y + K)) := by
      funext y; simp only [hg]; rw [add_comm K y]; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun x => 1 / x) K,
      integral_one_div_of_pos (by linarith) (by linarith)]
    congr 2 <;> simp only [hK, hE] <;> ring
  have hp1' : 0 ≤ 1 - p := by linarith
  have hfin : ∫ y in (0 : ℝ)..1, 1 / H y ≤ 1 - (1 - p) * ∫ y in (0 : ℝ)..1, g y := by
    nlinarith [mul_le_mul_of_nonneg_left hcheb hp1']
  have hHdef : (fun y => 1 / (1 / (p * s) - 1 + y * (1 - p * Real.log y))) = fun y => 1 / H y := rfl
  rw [hHdef, ← hgint]
  have hpinv : 0 < 1 / p := by positivity
  calc 1 / p * ∫ y in (0 : ℝ)..1, 1 / H y ≤ 1 / p * (1 - (1 - p) * ∫ y in (0 : ℝ)..1, g y) :=
        mul_le_mul_of_nonneg_left hfin hpinv.le
    _ = _ := by field_simp
