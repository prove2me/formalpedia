-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P07.rate_laplace_transform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:11:02.491375+00:00
-- url     : https://prove2.me/submissions/9a088902-0240-4e75-91ac-5856a248e947

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

/-- PDF p.26, Lemma B.1: numerator g(z)-g(0+)/2, visually checked in the PDF;
the Laplace integral is genuine throughout the open halfplane. -/

theorem g73n_mul_exp_neg_le_one' (u : ℝ) : u * Real.exp (-u) ≤ 1 := by
  have h := Real.add_one_le_exp u
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-u)]

theorem g73n_tE_bd (x : ℝ) (hx : 0 < x) (t : ℝ) :
    t * Real.exp (-(t * x)) ≤ (2 / x) * Real.exp (-(x / 2) * t) := by
  have h := g73n_mul_exp_neg_le_one' (x * t / 2)
  have e : Real.exp (-(t * x)) = Real.exp (-(x * t / 2)) * Real.exp (-(x / 2) * t) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(x / 2) * t) = Real.exp (-(x * t / 2)) := by ring_nf
  rw [e, e2]
  have hp := Real.exp_pos (-(x * t / 2))
  have : t * Real.exp (-(x * t / 2)) ≤ 2 / x := by
    rw [le_div_iff₀ hx]; nlinarith
  nlinarith

theorem g73n_normE (z : ℂ) (t : ℝ) : ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-(t * z.re)) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem g73n_hasDerivE (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) (Complex.exp (-(t : ℂ) * z) * (-z)) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(t : ℂ) * z) (-z) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.neg.mul_const z)
  exact h1.cexp

theorem g73n_intOn_tE (z : ℂ) (hz : 0 < z.re) (c : ℝ) (hc : 0 ≤ c) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * (t : ℂ)) (Ioi c) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi c (by linarith : 0 < z.re / 2)).const_mul (2 / z.re))
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ) * z) * (t : ℂ)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun t ht => ?_
  simp only [mem_Ioi] at ht
  rw [norm_mul, g73n_normE, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [mul_comm]; exact g73n_tE_bd _ hz t

theorem g73n_tendsto_tE (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => (t : ℂ) * Complex.exp (-(t : ℂ) * z)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hz)
  have h2 := h1.const_mul (1 / z.re)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  simp only [Function.comp, id, pow_one]
  rw [norm_mul, g73n_normE, Complex.norm_real, Real.norm_of_nonneg ht]
  field_simp

theorem g73n_tendsto_E (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [g73n_normE]
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hz))

noncomputable def g73n_G (z : ℂ) (t : ℝ) : ℂ := -((t : ℂ) / z + 1 / z ^ 2) * Complex.exp (-(t : ℂ) * z)

theorem g73n_hasDerivG (z : ℂ) (hz0 : z ≠ 0) (t : ℝ) :
    HasDerivAt (g73n_G z) (Complex.exp (-(t : ℂ) * z) * (t : ℂ)) t := by
  have hA : HasDerivAt (fun x : ℝ => (x : ℂ) / z) (((1 : ℝ) : ℂ) / z) t :=
    (hasDerivAt_id t).ofReal_comp.div_const z
  have := ((hA.mul (g73n_hasDerivE z t)).add ((g73n_hasDerivE z t).const_mul (1 / z ^ 2))).neg
  have hfun : g73n_G z = -(((fun x : ℝ => (x : ℂ) / z) * fun t : ℝ => Complex.exp (-(t : ℂ) * z)) +
      fun y : ℝ => 1 / z ^ 2 * Complex.exp (-(y : ℂ) * z)) := by
    funext x; simp only [g73n_G, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]; ring
  rw [hfun]; refine this.congr_deriv ?_; push_cast; field_simp; ring

theorem g73n_I1 (z : ℂ) (hz : 0 < z.re) :
    ∫ t in Ioi (0:ℝ), Complex.exp (-(t : ℂ) * z) * (t : ℂ) = 1 / z ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hlim : Tendsto (g73n_G z) atTop (𝓝 0) := by
    have := ((g73n_tendsto_tE z hz).const_mul (-(1 / z))).add ((g73n_tendsto_E z hz).const_mul (-(1 / z ^ 2)))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun t => ?_
    unfold g73n_G; field_simp; ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto
    (g73n_hasDerivG z hz0 0).continuousAt.continuousWithinAt
    (fun t _ => g73n_hasDerivG z hz0 t) (g73n_intOn_tE z hz 0 le_rfl) hlim]
  simp [g73n_G]

theorem g73n_I2 (z : ℂ) (hz : 0 < z.re) :
    ∫ t in Ioi (0:ℝ), Complex.exp (-(t : ℂ) * z) = 1 / z := by
  have := integral_exp_mul_complex_Ioi (a := -z) (by simp; linarith) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
  rw [← show (∫ x : ℝ in Ioi 0, Complex.exp (-z * x)) = ∫ t in Ioi (0:ℝ), Complex.exp (-(t : ℂ) * z) from
    integral_congr_ae (Eventually.of_forall fun t => by simp only; ring_nf), this]
  field_simp

theorem g73n_J (z : ℂ) (hz : 0 < z.re) (s : ℝ) (hs : 0 < s) :
    ∫ t in Ioi (0:ℝ), Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ) =
      (1 - Complex.exp (-(s : ℂ) * z)) / z ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ)) (Ioi 0) := by
    refine Integrable.mono' ((g73n_intOn_tE z hz 0 le_rfl).norm)
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    simp only [mem_Ioi] at ht
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (le_min hs.le ht.le),
      Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
  rw [← Ioc_union_Ioi_eq_Ioi hs.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hs.le))]
  have hA : ∫ t in Ioc 0 s, Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ) =
      g73n_G z s - g73n_G z 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ => Complex.exp (-(t : ℂ) * z) * (t : ℂ))
      (fun t ht => by simp only; rw [min_eq_right ht.2])]
    rw [← intervalIntegral.integral_of_le hs.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => g73n_hasDerivG z hz0 t)
      ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ) * z) * (t : ℂ)).intervalIntegrable 0 s)
  have hB : ∫ t in Ioi s, Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ) =
      (s : ℂ) * (Complex.exp (-(s : ℂ) * z) / z) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => (s : ℂ) * Complex.exp (-z * t))
      (fun t ht => by simp only; rw [min_eq_left (le_of_lt ht)]; ring_nf)]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simp; linarith)]
    congr 1; field_simp
  rw [hA, hB]
  unfold g73n_G
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, zero_div, zero_add, mul_one]
  field_simp
  ring

theorem g73n_ae_pos (g : BernsteinData) : ∀ᵐ s ∂g.mu, 0 < s := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext; simp
  rw [this]; exact g.support_positive

theorem g73n_sfinite (g : BernsteinData) : SFinite g.mu := by
  haveI : IsFiniteMeasure (g.mu.withDensity fun s => ENNReal.ofReal (s / (1 + s))) :=
    isFiniteMeasure_withDensity_ofReal g.levy_integrable.2
  have hm : Measurable fun s : ℝ => ENNReal.ofReal (s / (1 + s)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hac : g.mu ≪ g.mu.withDensity (fun s => ENNReal.ofReal (s / (1 + s))) := by
    refine withDensity_absolutelyContinuous' hm.aemeasurable ?_
    filter_upwards [g73n_ae_pos g] with s hs
    exact (ENNReal.ofReal_pos.mpr (div_pos hs (by linarith))).ne'
  exact sFinite_of_absolutelyContinuous hac

theorem g73n_min_bd (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : min s t ≤ (1 + t) * (2 * (s / (1 + s))) := by
  have h2 : min s 1 ≤ 2 * (s / (1 + s)) := by
    rw [mul_div_assoc', le_div_iff₀ (by linarith)]
    rcases le_or_gt s 1 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h.le]; linarith
  have h5 : min s t ≤ (1 + t) * min s 1 := by
    rcases le_or_gt s 1 with h | h
    · rw [min_eq_left h]; nlinarith [min_le_left s t]
    · rw [min_eq_right h.le]; nlinarith [min_le_right s t]
  calc min s t ≤ (1 + t) * min s 1 := h5
    _ ≤ _ := by gcongr

theorem g73n_int_min' (g : BernsteinData) (t : ℝ) (ht : 0 < t) :
    Integrable (fun s : ℝ => min s t) g.mu := by
  refine Integrable.mono' (g.levy_integrable.const_mul (2 * (1 + t)))
    (by fun_prop : Continuous fun s : ℝ => min s t).aestronglyMeasurable ?_
  filter_upwards [g73n_ae_pos g] with s hs
  rw [Real.norm_of_nonneg (le_min hs.le ht.le)]
  have := g73n_min_bd s t hs ht
  linarith

theorem g73n_rate_eq (g : BernsteinData) (t : ℝ) (ht : 0 < t) :
    t * bernsteinRate g t = g.a / 2 * t + g.b + ∫ s, min s t ∂g.mu := by
  unfold bernsteinRate
  rw [mul_add, mul_add, ← integral_const_mul]
  have : ∀ s : ℝ, t * min (s / t) 1 = min s t := by
    intro s; rw [mul_min_of_nonneg _ _ ht.le]; congr 1 <;> field_simp
  simp_rw [this]
  field_simp

theorem g73n_intOn_E (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) (Ioi 0) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hz)
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ) * z)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun t => ?_
  rw [g73n_normE]; ring_nf; exact le_rfl

theorem solution (g : BernsteinData) (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((t * bernsteinRate g t : ℝ) : ℂ)) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * z) * ((t * bernsteinRate g t : ℝ) : ℂ)) =
      (bernsteinValue g z - (g.a : ℂ) / 2) / z ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  haveI := g73n_sfinite g
  set x := z.re with hxdef
  set Lv := ∫ s, s / (1 + s) ∂g.mu with hLv
  have hpos := g73n_ae_pos g
  set Fc : ℝ → ℝ → ℂ := fun t s => Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ) with hFc
  have hFm : AEStronglyMeasurable (Function.uncurry Fc) ((volume.restrict (Ioi (0:ℝ))).prod g.mu) := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [hFc, Function.uncurry_def]
    fun_prop
  have hFint : Integrable (Function.uncurry Fc) ((volume.restrict (Ioi (0:ℝ))).prod g.mu) := by
    rw [integrable_prod_iff hFm]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun t ht => ?_
      simp only [Function.uncurry_apply_pair, hFc]
      exact ((g73n_int_min' g t ht).ofReal).const_mul _
    · refine Integrable.mono' (((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < x / 2))).const_mul
        (2 * Lv * (1 + 2 / x))) hFm.norm.integral_prod_right' ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun t ht => ?_
      simp only [mem_Ioi] at ht
      simp only [Function.uncurry_apply_pair, hFc]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have hb : ∫ s, ‖Complex.exp (-(t : ℂ) * z) * ((min s t : ℝ) : ℂ)‖ ∂g.mu ≤
          ∫ s, Real.exp (-(t * x)) * (1 + t) * 2 * (s / (1 + s)) ∂g.mu := by
        apply integral_mono_ae (((g73n_int_min' g t ht).ofReal).const_mul _).norm
        · have := g.levy_integrable.const_mul (Real.exp (-(t * x)) * (1 + t) * 2)
          simpa [mul_assoc] using this
        filter_upwards [hpos] with s hs
        rw [norm_mul, g73n_normE, Complex.norm_real, Real.norm_of_nonneg (le_min hs.le ht.le)]
        have := g73n_min_bd s t hs ht
        have he := Real.exp_pos (-(t * x))
        calc Real.exp (-(t * x)) * min s t ≤ Real.exp (-(t * x)) * ((1 + t) * (2 * (s / (1 + s)))) :=
              mul_le_mul_of_nonneg_left this he.le
          _ = _ := by ring
      refine hb.trans ?_
      rw [integral_const_mul]
      have hLv0 : 0 ≤ Lv := integral_nonneg_of_ae (by
        filter_upwards [hpos] with s hs; positivity)
      have h1 := g73n_tE_bd x (by linarith) t
      have h2 : Real.exp (-(t * x)) ≤ Real.exp (-(x / 2) * t) := Real.exp_le_exp.mpr (by nlinarith)
      have h3 : Real.exp (-(t * x)) * (1 + t) ≤ (1 + 2 / x) * Real.exp (-(x / 2) * t) := by nlinarith
      calc Real.exp (-(t * x)) * (1 + t) * 2 * Lv = 2 * Lv * (Real.exp (-(t * x)) * (1 + t)) := by ring
        _ ≤ 2 * Lv * ((1 + 2 / x) * Real.exp (-(x / 2) * t)) := by gcongr
        _ = _ := by ring
  -- Fubini
  have hswap := integral_integral_swap hFint
  have hleft : ∀ t : ℝ, ∫ s, Fc t s ∂g.mu =
      Complex.exp (-(t : ℂ) * z) * (((∫ s, min s t ∂g.mu) : ℝ) : ℂ) := by
    intro t; simp only [hFc]; rw [integral_const_mul]; congr 1; exact integral_complex_ofReal
  have hright : ∫ s, (∫ t in Ioi (0:ℝ), Fc t s) ∂g.mu =
      (∫ s, (1 - Complex.exp (-(s : ℂ) * z)) ∂g.mu) / z ^ 2 := by
    rw [← integral_div]
    refine integral_congr_ae ?_
    filter_upwards [hpos] with s hs
    exact g73n_J z hz s hs
  have hH : IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * (((∫ s, min s t ∂g.mu) : ℝ) : ℂ))
      (Ioi 0) := by
    have := hFint.integral_prod_left
    simp only [Function.uncurry_apply_pair] at this
    simp_rw [hleft] at this
    exact this
  have hI3 : ∫ t in Ioi (0:ℝ), Complex.exp (-(t : ℂ) * z) * (((∫ s, min s t ∂g.mu) : ℝ) : ℂ) =
      (∫ s, (1 - Complex.exp (-(s : ℂ) * z)) ∂g.mu) / z ^ 2 := by
    rw [← hright, ← hswap]
    simp_rw [hleft]
  have hcongr : EqOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((t * bernsteinRate g t : ℝ) : ℂ))
      (fun t : ℝ => ((g.a / 2 : ℝ) : ℂ) * (Complex.exp (-(t : ℂ) * z) * (t : ℂ)) +
        (g.b : ℂ) * Complex.exp (-(t : ℂ) * z) +
        Complex.exp (-(t : ℂ) * z) * (((∫ s, min s t ∂g.mu) : ℝ) : ℂ)) (Ioi 0) := by
    intro t ht
    simp only
    rw [g73n_rate_eq g t ht]
    push_cast
    ring
  have hA := (g73n_intOn_tE z hz 0 le_rfl).const_mul ((g.a / 2 : ℝ) : ℂ)
  have hB := (g73n_intOn_E z hz).const_mul (g.b : ℂ)
  have hAB : Integrable (fun t : ℝ => ((g.a / 2 : ℝ) : ℂ) * (Complex.exp (-(t : ℂ) * z) * (t : ℂ)) +
      (g.b : ℂ) * Complex.exp (-(t : ℂ) * z)) (volume.restrict (Ioi 0)) := hA.add hB
  have hsum := hAB.add hH
  constructor
  · exact (integrableOn_congr_fun hcongr measurableSet_Ioi).mpr hsum
  · rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    rw [integral_add hAB hH, integral_add hA hB, integral_const_mul, integral_const_mul,
      g73n_I1 z hz, g73n_I2 z hz, hI3]
    unfold bernsteinValue
    push_cast
    field_simp
    ring


end
