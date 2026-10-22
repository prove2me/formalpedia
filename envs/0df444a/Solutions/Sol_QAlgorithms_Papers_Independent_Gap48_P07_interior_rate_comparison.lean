-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P07.interior_rate_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:03:11.619792+00:00
-- url     : https://prove2.me/submissions/f80deb8e-3274-41bb-a21b-31713d94138f

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

theorem g73o_ae_pos (g : BernsteinData) : ∀ᵐ s ∂g.mu, 0 < s := by
  rw [ae_iff]
  have : {s : ℝ | ¬ 0 < s} = Iic 0 := by ext s; simp
  rw [this]; exact g.support_positive

theorem g73o_min_le (s : ℝ) (hs : 0 ≤ s) : min s 1 ≤ 2 * (s / (1 + s)) := by
  have h1 : 0 < 1 + s := by linarith
  rw [show 2 * (s / (1 + s)) = 2 * s / (1 + s) by ring, le_div_iff₀ h1]
  rcases le_total s 1 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

theorem g73o_min_mul (s c : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c) :
    min (s * c) 1 ≤ max c 1 * min s 1 := by
  rcases le_total s 1 with h | h
  · rw [min_eq_left h]
    calc min (s * c) 1 ≤ s * c := min_le_left _ _
      _ ≤ s * max c 1 := mul_le_mul_of_nonneg_left (le_max_left _ _) hs
      _ = max c 1 * s := by ring
  · rw [min_eq_right h]
    calc min (s * c) 1 ≤ 1 := min_le_right _ _
      _ ≤ max c 1 := le_max_right _ _
      _ = max c 1 * 1 := by ring

theorem g73o_integrable_min (g : BernsteinData) (t : ℝ) (ht : 0 < t) :
    Integrable (fun s => min (s / t) 1) g.mu := by
  refine (g.levy_integrable.const_mul (max (1 / t) 1 * 2)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [g73o_ae_pos g] with s hs
  have h0 : 0 ≤ min (s / t) 1 := le_min (by positivity) zero_le_one
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have := g73o_min_mul s (1 / t) hs.le (by positivity)
  rw [show s * (1 / t) = s / t by ring] at this
  calc min (s / t) 1 ≤ max (1 / t) 1 * min s 1 := this
    _ ≤ max (1 / t) 1 * (2 * (s / (1 + s))) :=
        mul_le_mul_of_nonneg_left (g73o_min_le s hs.le) (by positivity)
    _ = max (1 / t) 1 * 2 * (s / (1 + s)) := by ring

theorem g73o_cnorm (w : ℂ) (hw : 0 ≤ w.re) : ‖1 - Complex.exp (-w)‖ ≤ 2 * min ‖w‖ 1 := by
  rcases le_total ‖w‖ 1 with h | h
  · rw [min_eq_left h]
    have := Complex.norm_exp_sub_one_le (x := -w) (by simpa using h)
    rw [norm_sub_rev]; simpa using this
  · rw [min_eq_right h]
    calc ‖1 - Complex.exp (-w)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-w)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [Complex.norm_exp]
        have : Real.exp (-w).re ≤ 1 := Real.exp_le_one_iff.mpr (by simp; linarith)
        simp only [norm_one]; linarith
      _ = 2 * 1 := by ring

theorem g73o_pt (s : ℝ) (hs : 0 < s) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖1 - Complex.exp (-(s : ℂ) * z)‖ ≤ 2 * min (s * ‖z‖) 1 := by
  have h := g73o_cnorm ((s : ℂ) * z) (by simp [Complex.mul_re]; positivity)
  rw [show -(s : ℂ) * z = -((s : ℂ) * z) by ring]
  simpa [norm_mul, abs_of_pos hs] using h

theorem g73o_integrable_c (g : BernsteinData) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun s : ℝ => 1 - Complex.exp (-(s : ℂ) * z)) g.mu := by
  refine (g.levy_integrable.const_mul (2 * (max ‖z‖ 1 * 2))).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [g73o_ae_pos g] with s hs
  calc ‖1 - Complex.exp (-(s : ℂ) * z)‖ ≤ 2 * min (s * ‖z‖) 1 := g73o_pt s hs z hz
    _ ≤ 2 * (max ‖z‖ 1 * min s 1) := by
        gcongr; exact g73o_min_mul s ‖z‖ hs.le (norm_nonneg _)
    _ ≤ 2 * (max ‖z‖ 1 * (2 * (s / (1 + s)))) := by
        gcongr; exact g73o_min_le s hs.le
    _ = 2 * (max ‖z‖ 1 * 2) * (s / (1 + s)) := by ring

theorem g73o_rate_nonneg (g : BernsteinData) (t : ℝ) (ht : 0 < t) : 0 ≤ bernsteinRate g t := by
  unfold bernsteinRate
  have := g.a_nonneg; have := g.b_nonneg
  have : 0 ≤ ∫ s, min (s / t) 1 ∂g.mu := by
    apply integral_nonneg_of_ae
    filter_upwards [g73o_ae_pos g] with s hs
    exact le_min (by positivity) zero_le_one
  have : 0 ≤ g.b / t := by positivity
  linarith

theorem g73o_upper (g : BernsteinData) (t β : ℝ) (z : ℂ) (ht : 0 < t) (hz : 0 ≤ z.re)
    (hβ : 1 ≤ β) (htz : t * ‖z‖ ≤ β) :
    ‖bernsteinValue g z‖ ≤ 2 * β * bernsteinRate g t := by
  unfold bernsteinValue bernsteinRate
  have hm := g73o_integrable_min g t ht
  have key : ‖∫ s, 1 - Complex.exp (-(s : ℂ) * z) ∂g.mu‖ ≤
      ∫ s, 2 * β * min (s / t) 1 ∂g.mu := by
    refine norm_integral_le_of_norm_le (hm.const_mul _) ?_
    filter_upwards [g73o_ae_pos g] with s hs
    calc ‖1 - Complex.exp (-(s : ℂ) * z)‖ ≤ 2 * min (s * ‖z‖) 1 := g73o_pt s hs z hz
      _ ≤ 2 * min (s / t * β) 1 := by
          have : s * ‖z‖ ≤ s / t * β := by
            calc s * ‖z‖ = s / t * (t * ‖z‖) := by field_simp
              _ ≤ s / t * β := by gcongr
          exact mul_le_mul_of_nonneg_left (min_le_min_right _ this) (by norm_num)
      _ ≤ 2 * (max β 1 * min (s / t) 1) := by
          gcongr; exact g73o_min_mul _ _ (by positivity) (by linarith)
      _ = 2 * β * min (s / t) 1 := by rw [max_eq_left hβ]; ring
  rw [integral_const_mul] at key
  have ha := g.a_nonneg; have hb := g.b_nonneg
  have hnz : ‖z‖ ≤ β / t := by rw [le_div_iff₀ ht]; linarith
  have hn : ‖(g.a : ℂ) + (g.b : ℂ) * z + ∫ s, 1 - Complex.exp (-(s : ℂ) * z) ∂g.mu‖ ≤
      g.a + g.b * ‖z‖ + ‖∫ s, 1 - Complex.exp (-(s : ℂ) * z) ∂g.mu‖ := by
    refine (norm_add₃_le).trans ?_
    simp [abs_of_nonneg ha, abs_of_nonneg hb]
  have : g.b * ‖z‖ ≤ g.b * (β / t) := mul_le_mul_of_nonneg_left hnz hb
  have e1 : 2 * β * (g.a / 2 + g.b / t + ∫ s, min (s / t) 1 ∂g.mu) =
      β * g.a + g.b * (β / t) * 2 + 2 * β * ∫ s, min (s / t) 1 ∂g.mu := by ring
  rw [e1]
  have : g.a ≤ β * g.a := by nlinarith
  have : 0 ≤ g.b * (β / t) := by positivity
  linarith

theorem g73o_exp_lb (y : ℝ) (hy : 0 ≤ y) : min y 1 / 2 ≤ 1 - Real.exp (-y) := by
  have h1 : 0 < 1 + y := by linarith
  have he : Real.exp (-y) ≤ 1 / (1 + y) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le h1 (by linarith [Real.add_one_le_exp y])
  have := g73o_min_le y hy
  have e : 1 - 1 / (1 + y) = y / (1 + y) := by field_simp; ring
  linarith

theorem g73o_lower (g : BernsteinData) (t α : ℝ) (z : ℂ) (ht : 0 < t) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (htz : α ≤ t * z.re) :
    α / 2 * bernsteinRate g t ≤ (bernsteinValue g z).re := by
  have hz : 0 < z.re := by
    by_contra h; rw [not_lt] at h; nlinarith
  have hzt : α / t ≤ z.re := by rw [div_le_iff₀ ht]; linarith
  have hI := g73o_integrable_c g z hz.le
  have hm := g73o_integrable_min g t ht
  unfold bernsteinValue bernsteinRate
  have hre : (∫ s, 1 - Complex.exp (-(s : ℂ) * z) ∂g.mu).re =
      ∫ s, (1 - Complex.exp (-(s : ℂ) * z)).re ∂g.mu := (integral_re hI).symm
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero, hre]
  have key : ∫ s, α / 2 * min (s / t) 1 ∂g.mu ≤
      ∫ s, (1 - Complex.exp (-(s : ℂ) * z)).re ∂g.mu := by
    refine integral_mono_ae (hm.const_mul _) hI.re ?_
    filter_upwards [g73o_ae_pos g] with s hs
    have hr : (1 - Complex.exp (-(s : ℂ) * z)).re =
        1 - Real.exp (-(s * z.re)) * Real.cos (-(s * z.im)) := by
      simp [Complex.exp_re, Complex.mul_re]
    rw [hr]
    have hc := Real.cos_le_one (-(s * z.im))
    have hep := Real.exp_pos (-(s * z.re))
    have h1 : 1 - Real.exp (-(s * z.re)) ≤ 1 - Real.exp (-(s * z.re)) * Real.cos (-(s * z.im)) := by
      nlinarith
    have h2 := g73o_exp_lb (s * z.re) (by positivity)
    have h3 : α * min (s / t) 1 ≤ min (s * z.re) 1 := by
      rcases le_total (s / t) 1 with h | h
      · rw [min_eq_left h]
        refine le_min ?_ (by nlinarith [div_nonneg hs.le ht.le])
        calc α * (s / t) = s * (α / t) := by ring
          _ ≤ s * z.re := by gcongr
      · rw [min_eq_right h]
        refine le_min ?_ (by linarith)
        calc α * 1 = α := by ring
          _ ≤ α * (s / t) := by nlinarith
          _ = s * (α / t) := by ring
          _ ≤ s * z.re := by gcongr
    linarith
  rw [integral_const_mul] at key
  have ha := g.a_nonneg; have hb := g.b_nonneg
  have : g.b * (α / t) ≤ g.b * z.re := mul_le_mul_of_nonneg_left hzt hb
  have e1 : α / 2 * (g.a / 2 + g.b / t + ∫ s, min (s / t) 1 ∂g.mu) =
      α / 4 * g.a + g.b * (α / t) / 2 + α / 2 * ∫ s, min (s / t) 1 ∂g.mu := by ring
  rw [e1]
  have : α / 4 * g.a ≤ g.a := by nlinarith
  have : 0 ≤ g.b * (α / t) := by positivity
  linarith


/-- PDF p.18, Proposition 4.2: constants precede g,t,z. -/
theorem solution (alpha beta : ℝ) (ha : 0 < alpha) (hab : alpha ≤ beta) :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧ ∀ (g : BernsteinData) (t : ℝ) (z : ℂ),
      0 < t → 0 < z.re → alpha ≤ t * z.re → t * z.re ≤ t * ‖z‖ → t * ‖z‖ ≤ beta →
      c0 * bernsteinRate g t ≤ ‖bernsteinValue g z‖ ∧ ‖bernsteinValue g z‖ ≤ c1 * bernsteinRate g t := by
  refine ⟨min alpha 1 / 2, 2 * max beta 1, by positivity, by positivity, ?_⟩
  intro g t z ht hz h1 h2 h3
  constructor
  · calc min alpha 1 / 2 * bernsteinRate g t ≤ (bernsteinValue g z).re :=
          g73o_lower g t (min alpha 1) z ht (lt_min ha one_pos) (min_le_right _ _)
            ((min_le_left _ _).trans h1)
      _ ≤ ‖bernsteinValue g z‖ := Complex.re_le_norm _
  · exact g73o_upper g t (max beta 1) z ht hz.le (le_max_right _ _) (h3.trans (le_max_left _ _))


end
