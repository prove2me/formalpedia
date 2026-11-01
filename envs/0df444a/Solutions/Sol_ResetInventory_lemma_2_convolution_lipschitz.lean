-- Prove2me | solution 1 for ResetInventory.lemma_2_convolution_lipschitz
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:23:20.076217+00:00
-- url     : https://prove2.me/submissions/909d4244-a3e9-4b3c-b485-5ae36959b008

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory

private lemma abs_max_zero_sub (a b : ℝ) : |max 0 a - max 0 b| ≤ |a - b| := by
  rw [abs_le]
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · simp only [max_eq_right ha, max_eq_right hb]
    constructor <;> cases abs_cases (a - b) <;> linarith
  · simp only [max_eq_right ha, max_eq_left hb]
    constructor <;> cases abs_cases (a - b) <;> linarith
  · simp only [max_eq_left ha, max_eq_right hb]
    constructor <;> cases abs_cases (a - b) <;> linarith
  · simp only [max_eq_left ha, max_eq_left hb]
    constructor <;> cases abs_cases (a - b) <;> linarith

private lemma abs_min_one_sub (a b : ℝ) : |min 1 a - min 1 b| ≤ |a - b| := by
  rw [abs_le]
  rcases le_total 1 a with ha | ha <;> rcases le_total 1 b with hb | hb
  · simp only [min_eq_left ha, min_eq_left hb]
    constructor <;> cases abs_cases (a - b) <;> linarith
  · simp only [min_eq_left ha, min_eq_right hb]
    constructor <;> cases abs_cases (a - b) <;> linarith
  · simp only [min_eq_right ha, min_eq_left hb]
    constructor <;> cases abs_cases (a - b) <;> linarith
  · simp only [min_eq_right ha, min_eq_right hb]
    constructor <;> cases abs_cases (a - b) <;> linarith

theorem solution :
    ¬ (∀ (f g : ℝ → ℝ) (L M P : ℝ),
        Integrable f → Integrable g →
        (∀ x : ℝ, x < 0 → f x = 0) →
        (∀ x : ℝ, |f x| ≤ M) → (∀ x : ℝ, |g x| ≤ P) →
        (∀ x : ℝ, 0 ≤ x → ∀ y : ℝ, 0 ≤ y → |f x - f y| ≤ L * |x - y|) →
        ∀ x y : ℝ, |(∫ z, f (x - z) * g z) - ∫ z, f (y - z) * g z| ≤
          (L * ∫ z, |g z| + M * P) * |x - y|) := by
  intro H
  let f : ℝ → ℝ := (Set.Icc (0 : ℝ) 2).indicator (fun u => min 1 (2 - u))
  let g : ℝ → ℝ := (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g :=
    (integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Ioc
  have hf_Dom : Integrable ((Set.Icc (0 : ℝ) 2).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc
  have hf_meas : AEStronglyMeasurable f volume :=
    ((continuous_const.min (continuous_const.sub continuous_id)).measurable.indicator
      measurableSet_Icc).aestronglyMeasurable
  have hf_bound_ind : ∀ x : ℝ, ‖f x‖ ≤ (Set.Icc (0 : ℝ) 2).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    dsimp [f]
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 2
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, abs_le]
      have hmin1 : min 1 (2 - x) ≤ 1 := min_le_left 1 (2 - x)
      have hmin0 : 0 ≤ min 1 (2 - x) := le_min zero_le_one (by linarith [hx.2])
      constructor <;> linarith
    · simp [hx]
  have hf : Integrable f := hf_Dom.mono' hf_meas (Filter.Eventually.of_forall hf_bound_ind)
  have hf0 : ∀ x : ℝ, x < 0 → f x = 0 := by
    intro x hx
    dsimp [f]
    rw [Set.indicator_of_notMem]
    intro hmem
    linarith [hmem.1]
  have hfM : ∀ x : ℝ, |f x| ≤ 1 := by
    intro x
    have := hf_bound_ind x
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 2 <;> simp [hx]
  have hgP : ∀ x : ℝ, |g x| ≤ 1 := by
    intro x
    dsimp [g]
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1 <;> simp [hx]
  have hf_eq : ∀ x : ℝ, 0 ≤ x → f x = max 0 (min 1 (2 - x)) := by
    intro x hx
    dsimp [f]
    by_cases hx2 : x ≤ 2
    · have hmem : x ∈ Set.Icc (0 : ℝ) 2 := ⟨hx, hx2⟩
      rw [Set.indicator_of_mem hmem]
      have h0 : 0 ≤ min 1 (2 - x) := le_min zero_le_one (by linarith)
      exact (max_eq_right h0).symm
    · rw [Set.indicator_of_notMem (fun h => hx2 h.2)]
      have h0 : min 1 (2 - x) ≤ 0 := le_trans (min_le_right 1 (2 - x)) (by linarith)
      exact (max_eq_left h0).symm
  have hfL : ∀ x : ℝ, 0 ≤ x → ∀ y : ℝ, 0 ≤ y → |f x - f y| ≤ 1 * |x - y| := by
    intro x hx y hy
    rw [hf_eq x hx, hf_eq y hy, one_mul]
    refine (abs_max_zero_sub _ _).trans ((abs_min_one_sub _ _).trans ?_)
    have heq : (2 - x) - (2 - y) = -(x - y) := by ring
    rw [heq, abs_neg]
  have h1 := H f g 1 1 1 hf hg hf0 hfM hgP hfL 1 0
  have h_int1 : (fun z : ℝ => f (1 - z) * g z) = g := by
    ext z
    dsimp [f, g]
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 1
    · have hz2 : 1 - z ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz2]
      have hmin : min 1 (2 - (1 - z)) = 1 := min_eq_left (by linarith [hz.1])
      rw [hmin, mul_one]
    · simp [hz]
  have h_int0 : (fun z : ℝ => f (0 - z) * g z) = (fun _ => 0) := by
    ext z
    dsimp [f, g]
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 1
    · have hz2 : (0 : ℝ) - z ∉ Set.Icc (0 : ℝ) 2 := fun h => by linarith [hz.1, h.1]
      rw [Set.indicator_of_notMem hz2, zero_mul]
    · simp [hz]
  have hg_val : ∫ z, g z = 1 := by
    dsimp [g]
    rw [integral_indicator measurableSet_Ioc, MeasureTheory.setIntegral_const,
      MeasureTheory.Measure.real, Real.volume_Ioc]
    norm_num
  have h_not_int : ¬ Integrable (fun z : ℝ => |g z| + 1 * 1) := by
    intro hsum
    have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) := by
      have := hsum.sub hg.norm
      convert this using 1
      ext z
      simp [Real.norm_eq_abs]
    have htop := integrable_const_iff.mp hconst
    rcases htop with hone | hvol
    · norm_num at hone
    · have huniv : (volume : Measure ℝ) Set.univ < ⊤ := hvol.measure_univ_lt_top
      rw [Real.volume_univ] at huniv
      exact lt_irrefl ⊤ huniv
  have h_undef : (∫ z : ℝ, (|g z| + 1 * 1)) = 0 := integral_undef h_not_int
  rw [h_int1, h_int0, integral_zero, hg_val, h_undef] at h1
  norm_num at h1
