-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P07.logarithmic_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:21:21.189454+00:00
-- url     : https://prove2.me/submissions/48566e30-da0b-4803-8327-2c7ac665563f

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

theorem g73o_sfinite (g : BernsteinData) : SFinite g.mu := by
  set w : ℝ → ENNReal := fun s => ENNReal.ofReal (s / (1 + s))
  set v : ℝ → ENNReal := fun s => ENNReal.ofReal ((1 + s) / s)
  haveI : IsFiniteMeasure (g.mu.withDensity w) :=
    isFiniteMeasure_withDensity_ofReal g.levy_integrable.2
  have hw : Measurable w := by fun_prop
  have hv : Measurable v := by fun_prop
  have h1 : w * v =ᵐ[g.mu] 1 := by
    filter_upwards [g73o_ae_pos g] with s hs
    simp only [Pi.mul_apply, Pi.one_apply, w, v]
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show s / (1 + s) * ((1 + s) / s) = 1 by field_simp]; simp
  have : g.mu = (g.mu.withDensity w).withDensity v := by
    rw [← withDensity_mul g.mu hw hv, withDensity_congr_ae h1, withDensity_one]
  rw [this]; infer_instance

theorem g73o_hasDerivExp (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) (Complex.exp (-(t : ℂ) * z) * (-z)) t := by
  have h : HasDerivAt (fun u : ℂ => Complex.exp (-u * z)) (Complex.exp (-(t : ℂ) * z) * (-z)) (t : ℂ) := by
    have := ((hasDerivAt_id (t : ℂ)).neg.mul_const z).cexp
    simpa using this
  exact h.comp_ofReal

theorem g73o_expint (z : ℂ) (hz : 0 < z.re) (c : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) (Ioi c) ∧
    ∫ t in Ioi c, Complex.exp (-(t : ℂ) * z) = Complex.exp (-(c : ℂ) * z) / z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have ha : (-z).re < 0 := by simp; linarith
  have e : (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) = fun t : ℝ => Complex.exp (-z * t) := by
    funext t; ring_nf
  rw [e]
  refine ⟨integrableOn_exp_mul_complex_Ioi ha c, ?_⟩
  rw [integral_exp_mul_complex_Ioi ha c]
  field_simp

theorem g73o_kernel (z : ℂ) (hz : 0 < z.re) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ)) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ) =
      (1 - Complex.exp (-(s : ℂ) * z)) / z ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  obtain ⟨hi0, _⟩ := g73o_expint z hz 0
  obtain ⟨his, hIs⟩ := g73o_expint z hz s
  have hcont : Continuous (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ)) := by
    fun_prop
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ)) (Ioi 0) := by
    refine (hi0.norm.const_mul s).mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_min hs (le_of_lt ht))]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
  refine ⟨hint, ?_⟩
  rw [← Ioc_union_Ioi_eq_Ioi hs, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hs))]
  have h1 : ∫ t in Ioc 0 s, Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ) =
      ∫ t in Ioc 0 s, Complex.exp (-(t : ℂ) * z) * (t : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro t ht; simp only; rw [min_eq_right ht.2]
  have h2 : ∫ t in Ioi s, Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ) =
      ∫ t in Ioi s, Complex.exp (-(t : ℂ) * z) * (s : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht; simp only; rw [min_eq_left (le_of_lt ht)]
  rw [h1, h2, integral_mul_const, hIs, ← intervalIntegral.integral_of_le hs]
  set G : ℝ → ℂ := fun t => -((t : ℂ) / z) * Complex.exp (-(t : ℂ) * z) -
    Complex.exp (-(t : ℂ) * z) / z ^ 2
  have hG : ∀ t ∈ uIcc 0 s, HasDerivAt G (Complex.exp (-(t : ℂ) * z) * (t : ℂ)) t := by
    intro t _
    have hE := g73o_hasDerivExp z t
    have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have := ((hT.div_const z).neg.mul hE).sub (hE.div_const (z ^ 2))
    have h2 : HasDerivAt G (-(1 / z) * Complex.exp (-(t : ℂ) * z) + (-((t : ℂ) / z)) *
        (Complex.exp (-(t : ℂ) * z) * -z) - Complex.exp (-(t : ℂ) * z) * -z / z ^ 2) t := this
    refine h2.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ) * z) * (t : ℂ)).intervalIntegrable _ _)]
  simp only [G]
  push_cast
  simp only [neg_zero, zero_mul, Complex.exp_zero, zero_div]
  field_simp
  ring

theorem g73o_inv_sq_int : IntegrableOn (fun t : ℝ => ((1 + t) ^ 2)⁻¹) (Ioi 0) := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -(1 + t)⁻¹) (l := 0)
    ?_ ?_ ?_ ?_
  · exact ((continuous_const.add continuous_id).continuousAt.inv₀ (by norm_num)).neg.continuousWithinAt
  · intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : (1 + t) ≠ 0 := by linarith
    have := (((hasDerivAt_id t).const_add 1).inv h1).neg
    refine this.congr_deriv ?_
    simp only [id, neg_div, neg_neg, one_div]
  · intro t _; positivity
  · have : Tendsto (fun t : ℝ => (1 + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    simpa using this.neg

theorem g73o_cint (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => ((z + (t : ℂ)) * (1 + (t : ℂ)))⁻¹) (Ioi 0) := by
  set c := min z.re 1 with hc
  have hc0 : 0 < c := lt_min hz one_pos
  have hcont : ContinuousOn (fun t : ℝ => ((z + (t : ℂ)) * (1 + (t : ℂ)))⁻¹) (Ioi 0) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    refine mul_ne_zero ?_ ?_
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  refine (g73o_inv_sq_int.const_mul c⁻¹).mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hn1 : ‖(1 + (t : ℂ))‖ = 1 + t := by
    rw [show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hn2 : c * (1 + t) ≤ ‖z + (t : ℂ)‖ := by
    calc c * (1 + t) ≤ z.re + t := by
          have := min_le_left z.re 1; have := min_le_right z.re 1; nlinarith
      _ = (z + (t : ℂ)).re := by simp
      _ ≤ ‖z + (t : ℂ)‖ := Complex.re_le_norm _
  rw [norm_inv, norm_mul, hn1]
  have hp : 0 < c * (1 + t) := by positivity
  calc (‖z + (t : ℂ)‖ * (1 + t))⁻¹ ≤ (c * (1 + t) * (1 + t))⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact mul_le_mul_of_nonneg_right hn2 (by linarith)
    _ = c⁻¹ * ((1 + t) ^ 2)⁻¹ := by field_simp

theorem g73o_logS (z : ℂ) (hz : 0 < z.re) :
    logarithmicStieltjes z = ∫ t in Ioi (0 : ℝ), ((z + (t : ℂ)) * (1 + (t : ℂ)))⁻¹ := by
  have hint := g73o_cint z hz
  by_cases h1 : z = 1
  · subst h1
    simp only [logarithmicStieltjes, if_true]
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t : ℝ => -((1 : ℂ) + (t : ℂ))⁻¹) (m := 0)
      ((continuous_const.add Complex.continuous_ofReal).continuousAt.inv₀ (by norm_num)).neg.continuousWithinAt
      ?_ hint ?_]
    · simp
    · intro t ht
      have ht' : (0 : ℝ) < t := ht
      have hne : (1 : ℂ) + (t : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have hT : HasDerivAt (fun t : ℝ => (1 : ℂ) + (t : ℂ)) 1 t :=
        ((hasDerivAt_id t).ofReal_comp).const_add 1
      have := (hT.inv hne).neg
      refine this.congr_deriv ?_
      field_simp
      try ring
    · have : Tendsto (fun t : ℝ => (((1 + t)⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id))
      have := this.neg
      simp only [Complex.ofReal_zero, neg_zero] at this
      refine this.congr' (Eventually.of_forall fun t => ?_)
      push_cast; ring
  · unfold logarithmicStieltjes
    rw [if_neg h1]
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hslit : ∀ t : ℝ, 0 ≤ t → (t : ℂ) + z ∈ Complex.slitPlane := by
      intro t ht; left; simp; linarith
    have hslit1 : ∀ t : ℝ, 0 ≤ t → (t : ℂ) + 1 ∈ Complex.slitPlane := by
      intro t ht; left; simp; linarith
    set F : ℝ → ℂ := fun t => (Complex.log ((t : ℂ) + 1) - Complex.log ((t : ℂ) + z)) / (z - 1)
    have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (((z + (t : ℂ)) * (1 + (t : ℂ)))⁻¹) t := by
      intro t ht
      have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have hA := (hT.add_const 1).clog_real (hslit1 t ht)
      have hB := (hT.add_const z).clog_real (hslit t ht)
      have := (hA.sub hB).div_const (z - 1)
      refine this.congr_deriv ?_
      have n1 : (t : ℂ) + 1 ≠ 0 := Complex.slitPlane_ne_zero (hslit1 t ht)
      have n2 : (t : ℂ) + z ≠ 0 := Complex.slitPlane_ne_zero (hslit t ht)
      have n3 : z + (t : ℂ) ≠ 0 := by rwa [add_comm]
      have n4 : 1 + (t : ℂ) ≠ 0 := by rwa [add_comm]
      field_simp
      ring
    have hlim : Tendsto F atTop (𝓝 0) := by
      have hw : Tendsto (fun t : ℝ => 1 + (z - 1) * (((t + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 1) := by
        have : Tendsto (fun t : ℝ => (((t + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 0).comp
            (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id))
        simpa using (this.const_mul (z - 1)).const_add 1
      have hl : Tendsto (fun t : ℝ => Complex.log (1 + (z - 1) * (((t + 1)⁻¹ : ℝ) : ℂ))) atTop
          (𝓝 0) := by
        have := ((continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto).comp hw
        rw [Complex.log_one] at this
        exact this
      have hl2 := (hl.neg.div_const (z - 1))
      rw [neg_zero, zero_div] at hl2
      refine hl2.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have htp : (0 : ℝ) < t + 1 := by linarith
      have hne : (1 + (z - 1) * (((t + 1)⁻¹ : ℝ) : ℂ)) ≠ 0 := by
        intro h
        have h' : ((t : ℂ) + z) = ((t + 1 : ℝ) : ℂ) * (1 + (z - 1) * (((t + 1)⁻¹ : ℝ) : ℂ)) := by
          have : ((t + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htp.ne'
          have h1' : (t : ℂ) + 1 ≠ 0 := by exact_mod_cast htp.ne'
          have h2' : (1 : ℂ) + t ≠ 0 := by rw [add_comm]; exact h1'
          push_cast; field_simp; ring
        rw [h, mul_zero] at h'
        exact Complex.slitPlane_ne_zero (hslit t ht.le) h'
      have e1 : Complex.log ((t : ℂ) + z) =
          Real.log (t + 1) + Complex.log (1 + (z - 1) * (((t + 1)⁻¹ : ℝ) : ℂ)) := by
        rw [← Complex.log_ofReal_mul htp hne]
        congr 1
        have : ((t + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htp.ne'
        have h1' : (t : ℂ) + 1 ≠ 0 := by exact_mod_cast htp.ne'
        have h2' : (1 : ℂ) + t ≠ 0 := by rw [add_comm]; exact h1'
        push_cast; field_simp; ring
      have e2 : Complex.log ((t : ℂ) + 1) = Real.log (t + 1) := by
        rw [Complex.ofReal_log htp.le]; push_cast; ring_nf
      simp only [F, e1, e2]
      ring
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := F) (m := 0)
      (hd 0 le_rfl).continuousAt.continuousWithinAt (fun t ht => hd t (le_of_lt ht)) hint hlim]
    simp only [F, Complex.ofReal_zero, zero_add, Complex.log_one]
    ring

def g73o_mu : Measure ℝ≥0 :=
  Measure.map Real.toNNReal ((volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun t => ((Real.toNNReal ((1 + |t|)⁻¹) : ℝ≥0) : ENNReal)))

theorem g73o_w_meas : Measurable (fun t : ℝ => Real.toNNReal ((1 + |t|)⁻¹)) := by fun_prop

theorem g73o_transfer (φ : ℝ≥0 → ℝ) (hφ : Continuous φ) :
    (Integrable φ g73o_mu ↔
      IntegrableOn (fun t : ℝ => (1 + t)⁻¹ * φ (Real.toNNReal t)) (Ioi 0)) ∧
    ∫ s, φ s ∂g73o_mu = ∫ t in Ioi (0 : ℝ), (1 + t)⁻¹ * φ (Real.toNNReal t) := by
  have hae : (fun t : ℝ => Real.toNNReal ((1 + |t|)⁻¹) • φ (Real.toNNReal t)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => (1 + t)⁻¹ * φ (Real.toNNReal t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity), abs_of_pos ht']
  constructor
  · unfold g73o_mu
    rw [integrable_map_measure hφ.aestronglyMeasurable measurable_real_toNNReal.aemeasurable,
      integrable_withDensity_iff_integrable_smul g73o_w_meas]
    exact integrable_congr hae
  · unfold g73o_mu
    rw [integral_map measurable_real_toNNReal.aemeasurable hφ.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul g73o_w_meas]
    exact integral_congr_ae hae

theorem g73o_locfin : IsLocallyFiniteMeasure g73o_mu := by
  refine ⟨fun x => ⟨Iio (x + 1), Iio_mem_nhds (lt_add_one x), ?_⟩⟩
  unfold g73o_mu
  rw [Measure.map_apply measurable_real_toNNReal measurableSet_Iio]
  have hsub : Real.toNNReal ⁻¹' Iio (x + 1) ⊆ Iio ((x : ℝ) + 1) := by
    intro t ht
    simp only [mem_preimage, mem_Iio] at ht ⊢
    have h1 : t ≤ (Real.toNNReal t : ℝ) := Real.le_coe_toNNReal t
    have h2 : (Real.toNNReal t : ℝ) < ((x + 1 : ℝ≥0) : ℝ) := by exact_mod_cast ht
    push_cast at h2; linarith
  calc _ ≤ ((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t => ((Real.toNNReal ((1 + |t|)⁻¹) : ℝ≥0) : ENNReal))) (Iio ((x : ℝ) + 1)) :=
        measure_mono hsub
    _ = ∫⁻ t in Iio ((x : ℝ) + 1), ((Real.toNNReal ((1 + |t|)⁻¹) : ℝ≥0) : ENNReal)
          ∂(volume.restrict (Ioi (0 : ℝ))) := withDensity_apply _ measurableSet_Iio
    _ ≤ ∫⁻ t in Iio ((x : ℝ) + 1), 1 ∂(volume.restrict (Ioi (0 : ℝ))) := by
        refine lintegral_mono fun t => ?_
        have : (1 + |t|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg t])
        have : Real.toNNReal ((1 + |t|)⁻¹) ≤ 1 := by
          rw [Real.toNNReal_le_one]; exact this
        exact ENNReal.coe_le_one_iff.mpr this
    _ = volume (Iio ((x : ℝ) + 1) ∩ Ioi 0) := by
        rw [setLIntegral_one, Measure.restrict_apply measurableSet_Iio]
    _ < ⊤ := by
        have : Iio ((x : ℝ) + 1) ∩ Ioi 0 = Ioo 0 ((x : ℝ) + 1) := by
          ext t; simp [and_comm]
        rw [this, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top

theorem g73o_cast (x t : ℝ) : (((x : ℂ) + (t : ℂ)) * (1 + (t : ℂ)))⁻¹ =
    ((((x + t) * (1 + t))⁻¹ : ℝ) : ℂ) := by push_cast; ring

theorem g73o_real (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => ((x + t) * (1 + t))⁻¹) (Ioi 0) ∧
    (logarithmicStieltjes (x : ℂ)).re = ∫ t in Ioi (0 : ℝ), ((x + t) * (1 + t))⁻¹ := by
  have hz : 0 < (x : ℂ).re := by simpa using hx
  have hI := g73o_cint (x : ℂ) hz
  have hre : ∀ t : ℝ, RCLike.re ((((x : ℂ) + (t : ℂ)) * (1 + (t : ℂ)))⁻¹) = ((x + t) * (1 + t))⁻¹ := by
    intro t; rw [g73o_cast, RCLike.re_to_complex, Complex.ofReal_re]
  constructor
  · have := hI.re
    simp only [hre] at this
    exact this
  · rw [g73o_logS (x : ℂ) hz]
    have := (integral_re hI).symm
    simp only [hre] at this
    rw [RCLike.re_to_complex] at this
    exact this

theorem g73o_phi (x : ℝ) (hx : 0 < x) :
    Integrable (fun s : ℝ≥0 => Real.rpow (x + (s : ℝ)) (-1)) g73o_mu ∧
    ∫ s, Real.rpow (x + (s : ℝ)) (-1) ∂g73o_mu = ∫ t in Ioi (0 : ℝ), ((x + t) * (1 + t))⁻¹ := by
  have hc : Continuous (fun s : ℝ≥0 => Real.rpow (x + (s : ℝ)) (-1)) := by
    refine Continuous.rpow_const (by fun_prop) (fun s => Or.inl ?_)
    have := s.2; positivity
  obtain ⟨h1, h2⟩ := g73o_transfer _ hc
  have hae : ∀ t ∈ Ioi (0 : ℝ), (1 + t)⁻¹ * Real.rpow (x + ((Real.toNNReal t : ℝ≥0) : ℝ)) (-1) =
      ((x + t) * (1 + t))⁻¹ := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [Real.coe_toNNReal _ ht'.le]
    show (1 + t)⁻¹ * (x + t) ^ (-1 : ℝ) = _
    rw [Real.rpow_neg_one, mul_inv, mul_comm]
  constructor
  · rw [h1]
    exact (g73o_real x hx).1.congr_fun (fun t ht => (hae t ht).symm) measurableSet_Ioi
  · rw [h2]
    exact setIntegral_congr_fun measurableSet_Ioi hae


/-- PDF pp.11–12, Example 2.9: Stieltjes membership and its explicit integral;
the removable quotient at one is assigned one. -/
theorem solution :
    (fun z : PositiveReal => (logarithmicStieltjes (z.1 : ℂ)).re) ∈ StieltjesClass 1 ∧
    ∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun t : ℝ => ((z + (t : ℂ)) * (1 + (t : ℂ)))⁻¹) (Ioi 0) ∧
      logarithmicStieltjes z = ∫ t in Ioi (0 : ℝ), ((z + (t : ℂ)) * (1 + (t : ℂ)))⁻¹ := by
  refine ⟨⟨0, g73o_mu, le_rfl, g73o_locfin, ?_, ?_⟩, ?_⟩
  · exact (g73o_phi 1 one_pos).1
  · intro z
    refine ⟨(g73o_phi z.1 z.2).1, ?_⟩
    show (logarithmicStieltjes (z.1 : ℂ)).re = _
    rw [zero_add, (g73o_phi z.1 z.2).2]
    exact (g73o_real z.1 z.2).2
  · intro z hz
    exact ⟨g73o_cint z hz, g73o_logS z hz⟩


end
