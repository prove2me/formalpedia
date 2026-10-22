-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P07.bernstein_rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:49:17.910023+00:00
-- url     : https://prove2.me/submissions/c0a26106-ef22-47fb-8715-cf2d5b656bae

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07
noncomputable section

open Set Filter MeasureTheory

open scoped Topology NNReal

open QAlgorithms.Papers.Independent.Gap48.P07

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore graphPower)

open QAlgorithms.Papers.Independent.Renew46.P11
  (LaplaceImage Bernstein CompletelyMonotone SpecialBernstein StieltjesClass PositiveReal)

attribute [local instance] Classical.propDecidable

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- PDF pp.17–18, Lemma 4.1: all three inequalities, including the real part. -/

theorem g73n_norm_one_sub_exp_neg_le (w : ℂ) (hw : 0 ≤ w.re) : ‖1 - Complex.exp (-w)‖ ≤ ‖w‖ := by
  have hE1 : Real.exp (-w.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE0 : 0 < Real.exp (-w.re) := Real.exp_pos _
  have hE2 : 1 - w.re ≤ Real.exp (-w.re) := by have := Real.add_one_le_exp (-w.re); linarith
  have hc1 : Real.cos w.im ≤ 1 := Real.cos_le_one _
  have hc2 : 1 - w.im ^ 2 / 2 ≤ Real.cos w.im := Real.one_sub_sq_div_two_le_cos
  have hsc : Real.sin w.im ^ 2 + Real.cos w.im ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have key : ‖1 - Complex.exp (-w)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_re, Complex.neg_re, Complex.neg_im,
      Complex.sub_im, Complex.one_im, Complex.exp_im, Real.cos_neg, Real.sin_neg]
    set E := Real.exp (-w.re)
    set c := Real.cos w.im
    set sn := Real.sin w.im
    have e1 : (1 - E * c) * (1 - E * c) + (0 - E * -sn) * (0 - E * -sn) = (1 - E) ^ 2 + 2 * E * (1 - c) := by
      linear_combination E ^ 2 * hsc
    rw [e1]
    have f1 : (1 - E) ^ 2 ≤ w.re ^ 2 := by nlinarith
    have f2 : 2 * E * (1 - c) ≤ 2 * (1 - c) := by nlinarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp key

theorem g73n_norm_one_sub_exp_neg_le_two (w : ℂ) (hw : 0 ≤ w.re) : ‖1 - Complex.exp (-w)‖ ≤ 2 := by
  have : ‖Complex.exp (-w)‖ ≤ 1 := by
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr (by simp; linarith)
  calc ‖1 - Complex.exp (-w)‖ ≤ ‖(1:ℂ)‖ + ‖Complex.exp (-w)‖ := norm_sub_le _ _
    _ ≤ 2 := by simp at this ⊢; linarith

theorem g73n_mul_exp_neg_le (u : ℝ) : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
  have h := Real.add_one_le_exp u
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-u)]

theorem g73n_mul_exp_neg_le_one (u : ℝ) : u * Real.exp (-u) ≤ 1 := by
  have := g73n_mul_exp_neg_le u; linarith [Real.exp_pos (-u)]

/-- lower pointwise bound -/
theorem g73n_lower_pt (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (z : ℂ) (hz : 0 ≤ z.re) :
    (t * z.re) * Real.exp (-(t * z.re)) * min (s / t) 1 ≤ (1 - Complex.exp (-(s : ℂ) * z)).re := by
  have hre : (1 - Complex.exp (-(s : ℂ) * z)).re ≥ 1 - Real.exp (-(s * z.re)) := by
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_re]
    have : (-(s:ℂ) * z).re = -(s * z.re) := by simp
    rw [this]
    nlinarith [Real.exp_pos (-(s * z.re)), Real.cos_le_one (-(s:ℂ) * z).im]
  refine le_trans ?_ hre
  rcases le_or_gt s t with hst | hst
  · rw [min_eq_left ((div_le_one ht).mpr hst)]
    have e1 : Real.exp (-(t * z.re)) ≤ Real.exp (-(s * z.re)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have := g73n_mul_exp_neg_le (s * z.re)
    have h3 : t * z.re * Real.exp (-(t * z.re)) * (s / t) = (s * z.re) * Real.exp (-(t * z.re)) := by
      field_simp
    rw [h3]
    nlinarith [mul_nonneg hs.le hz]
  · rw [min_eq_right ((one_le_div ht).mpr hst.le)]
    have e1 : Real.exp (-(s * z.re)) ≤ Real.exp (-(t * z.re)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have := g73n_mul_exp_neg_le (t * z.re)
    linarith

theorem g73n_upper_pt (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖1 - Complex.exp (-(s : ℂ) * z)‖ ≤ max 2 (t * ‖z‖) * min (s / t) 1 := by
  have hw : 0 ≤ ((s : ℂ) * z).re := by simp; positivity
  have h1 := g73n_norm_one_sub_exp_neg_le ((s : ℂ) * z) hw
  have h2 := g73n_norm_one_sub_exp_neg_le_two ((s : ℂ) * z) hw
  rw [neg_mul]
  rcases le_or_gt s t with hst | hst
  · rw [min_eq_left ((div_le_one ht).mpr hst)]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le] at h1
    calc _ ≤ s * ‖z‖ := h1
      _ = (t * ‖z‖) * (s / t) := by field_simp
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · rw [min_eq_right ((one_le_div ht).mpr hst.le)]
    linarith [le_max_left 2 (t * ‖z‖)]

theorem g73n_min_le (s : ℝ) (hs : 0 < s) : min s 1 ≤ 2 * (s / (1 + s)) := by
  rw [mul_div_assoc', le_div_iff₀ (by linarith)]
  rcases le_or_gt s 1 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h.le]; linarith

theorem g73n_ae_pos (g : BernsteinData) : ∀ᵐ s ∂g.mu, 0 < s := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext; simp
  rw [this]; exact g.support_positive

theorem g73n_int_exp (g : BernsteinData) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun s : ℝ => 1 - Complex.exp (-(s : ℂ) * z)) g.mu := by
  refine Integrable.mono' (g.levy_integrable.const_mul (2 * (2 + ‖z‖))) ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ => 1 - Complex.exp (-(s : ℂ) * z)).aestronglyMeasurable
  · filter_upwards [g73n_ae_pos g] with s hs
    have h1 := g73n_upper_pt s 1 hs one_pos z hz
    have h2 := g73n_min_le s hs
    simp only [div_one, one_mul] at h1
    have h3 : max 2 ‖z‖ ≤ 2 + ‖z‖ := max_le (by linarith [norm_nonneg z]) (by linarith)
    have h4 : 0 ≤ min s 1 := le_min hs.le zero_le_one
    calc _ ≤ max 2 ‖z‖ * min s 1 := h1
      _ ≤ (2 + ‖z‖) * (2 * (s / (1 + s))) := by
        apply mul_le_mul h3 h2 h4; positivity
      _ = _ := by ring

theorem g73n_int_min (g : BernsteinData) (t : ℝ) (ht : 0 < t) :
    Integrable (fun s : ℝ => min (s / t) 1) g.mu := by
  refine Integrable.mono' (g.levy_integrable.const_mul (2 * (1 + 1 / t))) ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ => min (s / t) 1).aestronglyMeasurable
  · filter_upwards [g73n_ae_pos g] with s hs
    have h2 := g73n_min_le s hs
    have h0 : 0 ≤ min (s / t) 1 := le_min (by positivity) zero_le_one
    rw [Real.norm_of_nonneg h0]
    have h5 : min (s / t) 1 ≤ (1 + 1 / t) * min s 1 := by
      rcases le_or_gt s 1 with h | h
      · rw [min_eq_left h]
        calc min (s / t) 1 ≤ s / t := min_le_left _ _
          _ = (1 / t) * s := by ring
          _ ≤ (1 + 1 / t) * s := by nlinarith
      · rw [min_eq_right h.le]
        calc min (s / t) 1 ≤ 1 := min_le_right _ _
          _ ≤ (1 + 1 / t) * 1 := by have : 0 < 1 / t := by positivity
                                    linarith
    calc _ ≤ (1 + 1 / t) * min s 1 := h5
      _ ≤ (1 + 1 / t) * (2 * (s / (1 + s))) := by gcongr
      _ = _ := by ring

theorem solution (g : BernsteinData) (t : ℝ) (ht : 0 < t)
    (z : ℂ) (hz : 0 < z.re) :
    (t * z.re) * Real.exp (-(t * z.re)) * bernsteinRate g t ≤ (bernsteinValue g z).re ∧
    (bernsteinValue g z).re ≤ ‖bernsteinValue g z‖ ∧
    ‖bernsteinValue g z‖ ≤ max 2 (t * ‖z‖) * bernsteinRate g t := by
  have hz' : 0 ≤ z.re := hz.le
  have hI := g73n_int_exp g z hz'
  have hm := g73n_int_min g t ht
  have hpos := g73n_ae_pos g
  have ha := g.a_nonneg
  have hb := g.b_nonneg
  refine ⟨?_, Complex.re_le_norm _, ?_⟩
  · unfold bernsteinValue bernsteinRate
    have hre := integral_re hI
    simp only [RCLike.re_to_complex] at hre
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    rw [← hre]
    set c := (t * z.re) * Real.exp (-(t * z.re)) with hc
    have hc1 : c ≤ 1 := g73n_mul_exp_neg_le_one _
    have hc0 : 0 ≤ c := by positivity
    have hint : c * ∫ s, min (s / t) 1 ∂g.mu ≤ ∫ s, (1 - Complex.exp (-(s : ℂ) * z)).re ∂g.mu := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hm.const_mul c) hI.re
      filter_upwards [hpos] with s hs
      exact g73n_lower_pt s t hs ht z hz'
    have hbt : c * (g.b / t) ≤ g.b * z.re := by
      have : c * (g.b / t) = g.b * z.re * Real.exp (-(t * z.re)) := by rw [hc]; field_simp
      rw [this]
      have : Real.exp (-(t * z.re)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have : 0 ≤ g.b * z.re := by positivity
      nlinarith
    have hat : c * (g.a / 2) ≤ g.a := by nlinarith
    nlinarith
  · unfold bernsteinValue bernsteinRate
    set M := max 2 (t * ‖z‖)
    have hM2 : 2 ≤ M := le_max_left _ _
    have hMt : t * ‖z‖ ≤ M := le_max_right _ _
    have hint : ‖∫ s, (1 - Complex.exp (-(s : ℂ) * z)) ∂g.mu‖ ≤ M * ∫ s, min (s / t) 1 ∂g.mu := by
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      apply integral_mono_ae hI.norm (hm.const_mul M)
      filter_upwards [hpos] with s hs
      exact g73n_upper_pt s t hs ht z hz'
    have h1 : ‖(g.a : ℂ) + (g.b : ℂ) * z + ∫ s, (1 - Complex.exp (-(s : ℂ) * z)) ∂g.mu‖ ≤
        g.a + g.b * ‖z‖ + ‖∫ s, (1 - Complex.exp (-(s : ℂ) * z)) ∂g.mu‖ := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha,
        Real.norm_of_nonneg hb]
    have hbt : g.b * ‖z‖ ≤ M * (g.b / t) := by
      have : g.b * ‖z‖ = (t * ‖z‖) * (g.b / t) := by field_simp
      rw [this]; gcongr
    have hat : g.a ≤ M * (g.a / 2) := by nlinarith
    nlinarith


end
