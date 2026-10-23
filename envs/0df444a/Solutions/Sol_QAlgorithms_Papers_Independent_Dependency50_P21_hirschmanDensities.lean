-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P21.hirschmanDensities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:46:02.112996+00:00
-- url     : https://prove2.me/submissions/6946913b-7cf3-4243-9276-7d0ef19bb815

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

open Filter MeasureTheory Set

namespace X7Hirschman

/-- An even nonnegative function with a primitive having a limit at `+∞` is integrable. -/
lemma X7_integrable_of_even {g F : ℝ → ℝ} {l : ℝ} (hd : ∀ x, HasDerivAt F (g x) x)
    (hpos : ∀ x, 0 ≤ g x) (hev : ∀ x, g (-x) = g x) (htop : Tendsto F atTop (nhds l)) :
    Integrable g := by
  have h1 : IntegrableOn g (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x) (fun x _ => hpos x) htop
  have h2 : IntegrableOn g (Iic 0) := by
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ))
    have key : IntegrableOn (g ∘ Neg.neg) ((Neg.neg : ℝ → ℝ) ⁻¹' Iic 0) ↔
        IntegrableOn g (Iic 0) :=
      hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding
    rw [← key]
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Iic 0 = Ici 0 := by
      ext x; simp
    have hfun : (g ∘ Neg.neg) = g := by funext x; exact hev x
    rw [hpre, hfun]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ))]
  exact h2.union h1

/-- Antiderivative of `1 / (cosh x - c)` when `s > 0`, `s^2 + c^2 = 1`. -/
lemma X7_hasDeriv (c s : ℝ) (hs : 0 < s) (hcs : s ^ 2 + c ^ 2 = 1) (x : ℝ) :
    HasDerivAt (fun x => 2 / s * Real.arctan ((Real.exp x - c) / s))
      (1 / (Real.cosh x - c)) x := by
  have h1 : HasDerivAt (fun x => (Real.exp x - c) / s) (Real.exp x / s) x := by
    simpa using ((Real.hasDerivAt_exp x).sub_const c).div_const s
  have h2 := (h1.arctan).const_mul (2 / s)
  refine h2.congr_deriv ?_
  have hex : 0 < Real.exp x := Real.exp_pos x
  have hden : 0 < Real.cosh x - c := by
    have : c < 1 := by nlinarith
    have := Real.one_le_cosh x
    linarith
  have hne : Real.exp x ≠ 0 := hex.ne'
  have hsn : s ≠ 0 := hs.ne'
  have hq : (Real.exp x - c) ^ 2 + s ^ 2 ≠ 0 := by positivity
  have he : Real.exp x * (Real.exp x)⁻¹ = 1 := mul_inv_cancel₀ hne
  have key : (Real.exp x - c) ^ 2 + s ^ 2 = 2 * Real.exp x * (Real.cosh x - c) := by
    rw [Real.cosh_eq, Real.exp_neg]
    linear_combination hcs - he
  have hR : 2 / s * (1 / (1 + ((Real.exp x - c) / s) ^ 2) * (Real.exp x / s)) =
      2 * Real.exp x / ((Real.exp x - c) ^ 2 + s ^ 2) := by
    field_simp
    ring
  rw [hR, key]
  field_simp

lemma X7_cos_lt_cosh (c x : ℝ) (hc : c < 1) : 0 < Real.cosh x - c := by
  have := Real.one_le_cosh x; linarith

/-- `∫ 1/(cosh x - c) = (2/s) (π/2 + arctan (c/s))`. -/
lemma X7_integral (c s : ℝ) (hs : 0 < s) (hcs : s ^ 2 + c ^ 2 = 1) :
    Integrable (fun x => 1 / (Real.cosh x - c)) ∧
    ∫ x, 1 / (Real.cosh x - c) = 2 / s * (Real.pi / 2 + Real.arctan (c / s)) := by
  have hc : c < 1 := by nlinarith
  have htop : Tendsto (fun x => 2 / s * Real.arctan ((Real.exp x - c) / s)) atTop
      (nhds (2 / s * (Real.pi / 2))) := by
    refine Tendsto.const_mul _ ?_
    refine (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_
    refine Tendsto.atTop_div_const hs ?_
    exact tendsto_atTop_add_const_right _ _ Real.tendsto_exp_atTop
  have hbot : Tendsto (fun x => 2 / s * Real.arctan ((Real.exp x - c) / s)) atBot
      (nhds (2 / s * Real.arctan ((0 - c) / s))) := by
    refine Tendsto.const_mul _ ?_
    refine (Real.continuous_arctan.tendsto _).comp ?_
    exact ((Real.tendsto_exp_atBot).sub_const c).div_const s
  have hint : Integrable (fun x => 1 / (Real.cosh x - c)) := by
    refine X7_integrable_of_even (X7_hasDeriv c s hs hcs) ?_ ?_ htop
    · intro x; exact (one_div_pos.mpr (X7_cos_lt_cosh c x hc)).le
    · intro x; simp [Real.cosh_neg]
  refine ⟨hint, ?_⟩
  rw [integral_of_hasDerivAt_of_tendsto (X7_hasDeriv c s hs hcs) hint hbot htop]
  rw [zero_sub, neg_div, Real.arctan_neg]
  ring

lemma X7_arctan_cot (a : ℝ) (h0 : 0 < a) (h1 : a < Real.pi) :
    Real.arctan (Real.cos a / Real.sin a) = Real.pi / 2 - a := by
  have : Real.cos a / Real.sin a = Real.tan (Real.pi / 2 - a) := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [this, Real.arctan_tan] <;> linarith

/-- For `a ∈ (0, π)`, `∫ 1/(cosh x - cos a) = 2(π - a)/sin a`. -/
lemma X7_integral_cos (a : ℝ) (h0 : 0 < a) (h1 : a < Real.pi) :
    Integrable (fun x => 1 / (Real.cosh x - Real.cos a)) ∧
    ∫ x, 1 / (Real.cosh x - Real.cos a) = 2 * (Real.pi - a) / Real.sin a := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi h0 h1
  obtain ⟨hi, he⟩ := X7_integral (Real.cos a) (Real.sin a) hs (Real.sin_sq_add_cos_sq a)
  refine ⟨hi, ?_⟩
  rw [he, X7_arctan_cot a h0 h1]
  field_simp
  ring

/-- Scaled version: `∫ K/(cosh (π t) - cos a) dt = K * 2(π-a)/(π sin a)`. -/
lemma X7_scaled (a K : ℝ) (h0 : 0 < a) (h1 : a < Real.pi) :
    Integrable (fun t => K / (Real.cosh (Real.pi * t) - Real.cos a)) ∧
    ∫ t, K / (Real.cosh (Real.pi * t) - Real.cos a) =
      K * (2 * (Real.pi - a) / Real.sin a) / Real.pi := by
  obtain ⟨hi, he⟩ := X7_integral_cos a h0 h1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfun : (fun t => K / (Real.cosh (Real.pi * t) - Real.cos a)) =
      fun t => K * (fun x => 1 / (Real.cosh x - Real.cos a)) (Real.pi * t) := by
    funext t; simp [div_eq_mul_inv]
  rw [hfun]
  refine ⟨(hi.comp_mul_left' hpi).const_mul K, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun x => 1 / (Real.cosh x - Real.cos a)) Real.pi, he]
  rw [abs_of_pos (inv_pos.mpr Real.pi_pos), smul_eq_mul]
  field_simp

lemma X7_betaZero_deriv (x : ℝ) :
    HasDerivAt (fun x => -2 / (Real.exp x + 1)) (1 / (Real.cosh x + 1)) x := by
  have hex : 0 < Real.exp x := Real.exp_pos x
  have h := (hasDerivAt_const x (-2:ℝ)).div ((Real.hasDerivAt_exp x).add_const 1)
    (by positivity)
  refine h.congr_deriv ?_
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

lemma X7_betaZero_integral :
    Integrable (fun x => 1 / (Real.cosh x + 1)) ∧ ∫ x, 1 / (Real.cosh x + 1) = 2 := by
  have htop : Tendsto (fun x => -2 / (Real.exp x + 1)) atTop (nhds 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    exact tendsto_atTop_add_const_right _ _ Real.tendsto_exp_atTop
  have hbot : Tendsto (fun x => -2 / (Real.exp x + 1)) atBot (nhds (-2 / (0 + 1))) := by
    refine Tendsto.div tendsto_const_nhds ?_ (by norm_num)
    exact (Real.tendsto_exp_atBot).add_const 1
  have hint : Integrable (fun x => 1 / (Real.cosh x + 1)) := by
    refine X7_integrable_of_even X7_betaZero_deriv ?_ ?_ htop
    · intro x; have := Real.one_le_cosh x; positivity
    · intro x; simp [Real.cosh_neg]
  refine ⟨hint, ?_⟩
  rw [integral_of_hasDerivAt_of_tendsto X7_betaZero_deriv hint hbot htop]
  norm_num

end X7Hirschman

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P21 X7Hirschman in
theorem solution :
    (∀ theta : ℝ, 0 < theta → theta < 1 →
      (∀ t, 0 ≤ alphaDensity theta t ∧ 0 ≤ betaDensity theta t) ∧
      Integrable (alphaDensity theta) ∧ Integrable (betaDensity theta) ∧
      (∫ t : ℝ, alphaDensity theta t) = 1 ∧ (∫ t : ℝ, betaDensity theta t) = 1) ∧
    (∀ t, Tendsto (fun theta : ℝ => betaDensity theta t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (betaZero t))) ∧
    (∀ t, 0 ≤ betaZero t) ∧ Integrable betaZero ∧ (∫ t : ℝ, betaZero t) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ h0 h1
    have hpθ : 0 < Real.pi * θ := mul_pos Real.pi_pos h0
    have hpθ1 : Real.pi * θ < Real.pi := by nlinarith [Real.pi_pos]
    have hsin : 0 < Real.sin (Real.pi * θ) := Real.sin_pos_of_pos_of_lt_pi hpθ hpθ1
    have hcos1 : Real.cos (Real.pi * θ) < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hpθ1.le hpθ
      simpa using this
    have hcos2 : -1 < Real.cos (Real.pi * θ) := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hpθ.le le_rfl hpθ1
      simpa using this
    -- α as a scaled kernel with a = πθ
    have hαfun : alphaDensity θ = fun t => (Real.sin (Real.pi * θ) / (2 * (1 - θ))) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) := by
      funext t; unfold alphaDensity; rw [div_div]
    -- β with a = π - πθ
    have hcosβ : Real.cos (Real.pi - Real.pi * θ) = - Real.cos (Real.pi * θ) :=
      Real.cos_pi_sub _
    have hsinβ : Real.sin (Real.pi - Real.pi * θ) = Real.sin (Real.pi * θ) :=
      Real.sin_pi_sub _
    have hβfun : betaDensity θ = fun t => (Real.sin (Real.pi * θ) / (2 * θ)) /
        (Real.cosh (Real.pi * t) - Real.cos (Real.pi - Real.pi * θ)) := by
      funext t; unfold betaDensity; rw [div_div, hcosβ, sub_neg_eq_add]
    obtain ⟨hαi, hαe⟩ := X7_scaled (Real.pi * θ) (Real.sin (Real.pi * θ) / (2 * (1 - θ)))
      hpθ hpθ1
    obtain ⟨hβi, hβe⟩ := X7_scaled (Real.pi - Real.pi * θ) (Real.sin (Real.pi * θ) / (2 * θ))
      (by linarith) (by linarith)
    have h1θ : 0 < 1 - θ := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t
      have hc := Real.one_le_cosh (Real.pi * t)
      constructor
      · unfold alphaDensity
        apply div_nonneg hsin.le
        apply mul_nonneg (by positivity); linarith
      · unfold betaDensity
        apply div_nonneg hsin.le
        apply mul_nonneg (by positivity); linarith
    · rw [hαfun]; exact hαi
    · rw [hβfun]; exact hβi
    · rw [hαfun, hαe]
      field_simp
    · rw [hβfun, hβe, hsinβ]
      field_simp
      ring
  · intro t
    have hc := Real.one_le_cosh (Real.pi * t)
    -- sin(πθ)/θ → π
    have hd : HasDerivAt (fun θ : ℝ => Real.sin (Real.pi * θ)) Real.pi 0 := by
      have := ((hasDerivAt_id (0:ℝ)).const_mul Real.pi).sin
      simpa using this
    have hslope := hd.tendsto_slope_zero
    have hs2 : Tendsto (fun θ : ℝ => Real.sin (Real.pi * θ) / θ) (nhdsWithin 0 (Set.Ioi 0))
        (nhds Real.pi) := by
      have := hslope.mono_left (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Ioi (0:ℝ)) =>
        (ne_of_gt hx)))
      refine this.congr' ?_
      filter_upwards with θ
      simp [div_eq_inv_mul]
    have hden : Tendsto (fun θ : ℝ => 2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * (Real.cosh (Real.pi * t) + 1))) := by
      have : Continuous (fun θ : ℝ => 2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) :=
        by fun_prop
      have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have hlim := hs2.div hden (by positivity)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
    rw [Pi.div_apply, div_div]
    unfold betaDensity
    ring
  · intro t
    unfold betaZero
    have := Real.one_le_cosh (Real.pi * t)
    positivity
  · obtain ⟨hi, he⟩ := X7_betaZero_integral
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hfun : betaZero = fun t => (Real.pi / 2) *
        (fun x => 1 / (Real.cosh x + 1)) (Real.pi * t) := by
      funext t; unfold betaZero; field_simp
    rw [hfun]
    refine ⟨(hi.comp_mul_left' hpi).const_mul _, ?_⟩
    rw [integral_const_mul, Measure.integral_comp_mul_left
      (fun x => 1 / (Real.cosh x + 1)) Real.pi, he]
    rw [abs_of_pos (inv_pos.mpr Real.pi_pos), smul_eq_mul]
    field_simp
