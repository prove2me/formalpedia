-- Prove2me | solution 1 for TeschlQM.Herglotz.herglotz_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:05:36.658537+00:00
-- url     : https://prove2.me/submissions/a826177b-288e-40d8-9da3-7416b4f50003

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_IsHerglotz
import Definitions.Def_TeschlQM_Herglotz_borelTransform

set_option autoImplicit false

open MeasureTheory Filter Topology Complex
open scoped Interval BoundedContinuousFunction

namespace HerglotzRepr1b26

/-- Poisson-type kernel `1/(w-z) - 1/(w - conj z)`. -/
noncomputable def kz (z w : ℂ) : ℂ := (z - (starRingEnd ℂ) z) / ((w - z) * (w - (starRingEnd ℂ) z))

lemma sub_conj_eq (z : ℂ) : z - (starRingEnd ℂ) z = 2 * z.im * I := by
  apply Complex.ext <;> simp <;> ring

lemma kz_real (z : ℂ) (x : ℝ) :
    kz z x = (2 * z.im * I) * ((((x - z.re) ^ 2 + z.im ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hden : ((x : ℂ) - z) * ((x : ℂ) - (starRingEnd ℂ) z) = (((x - z.re) ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
      simp only [mul_re, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im]
      ring
    · rw [Complex.ofReal_im]
      simp only [mul_im, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im]
      ring
  rw [kz, sub_conj_eq, hden, div_eq_mul_inv, Complex.ofReal_inv]

lemma lorentz_eq (a y x : ℝ) (hy : 0 < y) :
    ((x - a) ^ 2 + y ^ 2)⁻¹ = (y ^ 2)⁻¹ * (1 + ((x - a) / y) ^ 2)⁻¹ := by
  rw [← mul_inv]
  congr 1
  field_simp
  ring

lemma integrable_lorentz (a y : ℝ) (hy : 0 < y) :
    Integrable (fun x : ℝ => ((x - a) ^ 2 + y ^ 2)⁻¹) := by
  have h := ((integrable_inv_one_add_sq.comp_div hy.ne').comp_sub_right a).const_mul ((y ^ 2)⁻¹)
  refine h.congr (Eventually.of_forall (fun x => ?_))
  simp only []
  rw [lorentz_eq a y x hy]

lemma integral_lorentz (a y : ℝ) (hy : 0 < y) :
    ∫ x : ℝ, ((x - a) ^ 2 + y ^ 2)⁻¹ = Real.pi / y := by
  simp_rw [lorentz_eq a y _ hy]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun u => (1 + (u / y) ^ 2)⁻¹) a]
  rw [Measure.integral_comp_div (fun u => (1 + u ^ 2)⁻¹) y, integral_univ_inv_one_add_sq]
  rw [abs_of_pos hy, smul_eq_mul]
  field_simp

lemma integral_kz (z : ℂ) (hz : 0 < z.im) :
    ∫ x : ℝ, kz z x = 2 * Real.pi * I := by
  simp_rw [kz_real]
  rw [integral_const_mul, integral_complex_ofReal, integral_lorentz _ _ hz]
  have hz' : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  push_cast
  field_simp

lemma norm_kz_real (z : ℂ) (hz : 0 < z.im) (x : ℝ) :
    ‖kz z x‖ = 2 * z.im * ((x - z.re) ^ 2 + z.im ^ 2)⁻¹ := by
  have hp : 0 < (x - z.re) ^ 2 + z.im ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hz 2)
  rw [kz_real, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]
  congr 1
  simp [abs_of_pos hz]

/-- Edge bound for the kernel. -/
lemma norm_kz_le (z w : ℂ) (hz : 0 < z.im) (R : ℝ) (hR : 2 * (|z.re| + z.im) ≤ R)
    (hw : w.im = R ∨ |w.re| = R) :
    ‖kz z w‖ ≤ 8 * z.im / R ^ 2 := by
  have hRe0 := abs_nonneg z.re
  have hRpos : 0 < R := by linarith
  have h1 : R / 2 ≤ ‖w - z‖ := by
    rcases hw with h | h
    · have := Complex.abs_im_le_norm (w - z)
      rw [sub_im, h] at this
      have := le_abs_self (R - z.im)
      linarith
    · have := Complex.abs_re_le_norm (w - z)
      rw [sub_re] at this
      have := abs_sub_abs_le_abs_sub w.re z.re
      rw [h] at this
      linarith
  have h2 : R / 2 ≤ ‖w - (starRingEnd ℂ) z‖ := by
    rcases hw with h | h
    · have := Complex.abs_im_le_norm (w - (starRingEnd ℂ) z)
      rw [sub_im, h, conj_im] at this
      have := le_abs_self (R - -z.im)
      linarith
    · have := Complex.abs_re_le_norm (w - (starRingEnd ℂ) z)
      rw [sub_re, conj_re] at this
      have := abs_sub_abs_le_abs_sub w.re z.re
      rw [h] at this
      linarith
  have hn : ‖z - (starRingEnd ℂ) z‖ = 2 * z.im := by
    rw [sub_conj_eq]
    simp [abs_of_pos hz]
  rw [kz, norm_div, norm_mul, hn]
  have hp : 0 < R / 2 := by positivity
  calc 2 * z.im / (‖w - z‖ * ‖w - (starRingEnd ℂ) z‖)
      ≤ 2 * z.im / ((R / 2) * (R / 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul h1 h2 hp.le (by positivity)
    _ = 8 * z.im / R ^ 2 := by field_simp; ring

/-- Counterclockwise boundary integral over the rectangle `[-R,R] × [0,R]`. -/
noncomputable def RI (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  (∫ x : ℝ in -R..R, f x) - (∫ x : ℝ in -R..R, f (x + R * I)) +
    I • (∫ y : ℝ in (0 : ℝ)..R, f (R + y * I)) - I • (∫ y : ℝ in (0 : ℝ)..R, f (-R + y * I))

lemma RI_eq_zero (f : ℂ → ℂ) (R : ℝ) (hR : 0 ≤ R) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[-R, R]] ×ℂ [[0, R]]))
    (Hd : ∀ x ∈ Set.Ioo (-R) R ×ℂ Set.Ioo 0 R \ s, DifferentiableAt ℂ f x) :
    RI f R = 0 := by
  have m1 : min (-R) R = -R := min_eq_left (by linarith)
  have m2 : max (-R) R = R := max_eq_right (by linarith)
  have m3 : min 0 R = 0 := min_eq_left hR
  have m4 : max 0 R = R := max_eq_right hR
  have h := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f
    ((-R : ℝ) : ℂ) ((R : ℂ) + R * I) s hs (by simpa using Hc) (by
      intro x hx
      apply Hd
      simpa [m1, m2, m3, m4] using hx)
  simpa [RI] using h

lemma mem_rect {R : ℝ} {w : ℂ} : w ∈ [[-R, R]] ×ℂ [[0, R]] ↔ w.re ∈ [[-R, R]] ∧ w.im ∈ [[0, R]] :=
  Iff.rfl

lemma RI_cauchy (G : ℂ → ℂ) (hd : ∀ w : ℂ, 0 ≤ w.im → DifferentiableAt ℂ G w) (z : ℂ)
    (hz : 0 < z.im) (R : ℝ) (hR1 : |z.re| < R) (hR2 : z.im < R) :
    RI (fun w => G w * kz z w) R = G z * RI (fun w => (w - z)⁻¹) R := by
  have hR : 0 ≤ R := le_trans (abs_nonneg _) hR1.le
  set c := (starRingEnd ℂ) z with hc
  have hcz : z - c ≠ 0 := by
    rw [hc, sub_conj_eq]
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    simp [this, Complex.I_ne_zero]
  have hne_c : ∀ w : ℂ, 0 ≤ w.im → w - c ≠ 0 := by
    intro w hw h0
    have := congrArg Complex.im h0
    simp [hc] at this
    linarith
  let h : ℂ → ℂ := fun w => G w * (z - c) / (w - c)
  have hdh : ∀ w : ℂ, 0 ≤ w.im → DifferentiableAt ℂ h w := fun w hw =>
    ((hd w hw).mul_const _).div (differentiableAt_id.sub_const _) (hne_c w hw)
  have hhz : h z = G z := by
    simp only [h]
    field_simp
  have key : ∀ w : ℂ, 0 ≤ w.im → w ≠ z →
      G w * kz z w = dslope h z w + G z * (w - z)⁻¹ := by
    intro w hw hwz
    rw [dslope_of_ne _ hwz, slope_def_field, hhz]
    simp only [h, kz]
    have h1 := hne_c w hw
    have h2 : w - z ≠ 0 := sub_ne_zero.2 hwz
    rw [← hc]
    field_simp
    ring
  have Hc : ContinuousOn (dslope h z) ([[-R, R]] ×ℂ [[0, R]]) := by
    intro w hw
    have hwim : 0 ≤ w.im := by
      have := (mem_rect.1 hw).2
      rw [Set.uIcc_of_le hR] at this
      exact this.1
    apply ContinuousAt.continuousWithinAt
    by_cases hwz : w = z
    · subst hwz
      exact continuousAt_dslope_same.2 (hdh w hwim)
    · exact (continuousAt_dslope_of_ne hwz).2 (hdh w hwim).continuousAt
  have Hd : ∀ x ∈ Set.Ioo (-R) R ×ℂ Set.Ioo 0 R \ {z}, DifferentiableAt ℂ (dslope h z) x := by
    intro x hx
    have hxz : x ≠ z := hx.2
    have hxim : 0 ≤ x.im := le_of_lt hx.1.2.1
    exact (differentiableAt_dslope_of_ne hxz).2 (hdh x hxim)
  have hzero := RI_eq_zero (dslope h z) R hR {z} (Set.countable_singleton z) Hc Hd
  have hedge : ∀ (p : ℝ → ℂ) (α β : ℝ), Continuous p →
      (∀ t ∈ [[α, β]], p t ∈ [[-R, R]] ×ℂ [[0, R]] ∧ p t ≠ z) →
      ∫ t in α..β, G (p t) * kz z (p t) =
        (∫ t in α..β, dslope h z (p t)) + G z * ∫ t in α..β, (p t - z)⁻¹ := by
    intro p α β hp hpt
    have hcont1 : ContinuousOn (fun t => dslope h z (p t)) [[α, β]] :=
      Hc.comp hp.continuousOn (fun t ht => (hpt t ht).1)
    have hcont2 : ContinuousOn (fun t => (p t - z)⁻¹) [[α, β]] :=
      ((hp.sub continuous_const).continuousOn).inv₀ (fun t ht => sub_ne_zero.2 (hpt t ht).2)
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hcont1.intervalIntegrable
        (hcont2.intervalIntegrable.const_mul _)]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have hm := (hpt t ht).1
    have hwim : 0 ≤ (p t).im := by
      have := (mem_rect.1 hm).2
      rw [Set.uIcc_of_le hR] at this
      exact this.1
    exact key (p t) hwim (hpt t ht).2
  have hRR : [[-R, R]] = Set.Icc (-R) R := Set.uIcc_of_le (by linarith)
  have h0R : [[0, R]] = Set.Icc 0 R := Set.uIcc_of_le hR
  have hz1 := abs_lt.1 hR1
  have e1 := hedge (fun x : ℝ => (x : ℂ)) (-R) R (by fun_prop) (fun t ht => by
    refine ⟨mem_rect.2 ⟨by simpa using ht, by simp [h0R, hR]⟩, fun h0 => ?_⟩
    have := congrArg Complex.im h0
    simp at this
    linarith)
  have e2 := hedge (fun x : ℝ => (x : ℂ) + R * I) (-R) R (by fun_prop) (fun t ht => by
    refine ⟨mem_rect.2 ⟨by simpa using ht, by simp [h0R, hR]⟩, fun h0 => ?_⟩
    have := congrArg Complex.im h0
    simp at this
    linarith)
  have e3 := hedge (fun y : ℝ => (R : ℂ) + y * I) 0 R (by fun_prop) (fun t ht => by
    refine ⟨mem_rect.2 ⟨by simp [hRR, hR], by simpa using ht⟩, fun h0 => ?_⟩
    have := congrArg Complex.re h0
    simp at this
    linarith)
  have e4 := hedge (fun y : ℝ => -(R : ℂ) + y * I) 0 R (by fun_prop) (fun t ht => by
    refine ⟨mem_rect.2 ⟨by simp [hRR, hR], by simpa using ht⟩, fun h0 => ?_⟩
    have := congrArg Complex.re h0
    simp at this
    linarith)
  simp only [RI] at hzero ⊢
  rw [e1, e2, e3, e4]
  simp only [smul_eq_mul] at hzero ⊢
  linear_combination hzero

/-- The rectangle boundary integrals converge to the integral over the real line. -/
lemma RI_tendsto (G : ℂ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ w : ℂ, 0 ≤ w.im → ContinuousAt G w)
    (hb : ∀ w : ℂ, 0 ≤ w.im → ‖G w‖ ≤ C) (z : ℂ) (hz : 0 < z.im) :
    Tendsto (fun R : ℝ => RI (fun w => G w * kz z w) R) atTop
      (𝓝 (∫ x : ℝ, G x * kz z x)) := by
  have hkc : ∀ x : ℝ, ContinuousAt (fun t : ℝ => kz z t) x := by
    intro x
    have hp : 0 < (x - z.re) ^ 2 + z.im ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hz 2)
    have : (fun t : ℝ => kz z t) =
        fun t : ℝ => (2 * z.im * I) * ((((t - z.re) ^ 2 + z.im ^ 2)⁻¹ : ℝ) : ℂ) :=
      funext (kz_real z)
    rw [this]
    refine continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp ?_)
    exact ((continuous_id.sub continuous_const).pow 2 |>.add continuous_const).continuousAt.inv₀
      hp.ne'
  have hint : Integrable (fun x : ℝ => G x * kz z x) := by
    refine Integrable.mono' ((integrable_lorentz z.re z.im hz).const_mul (C * (2 * z.im))) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      rw [continuous_iff_continuousAt]
      intro x
      exact ((hc x (by simp)).comp Complex.continuous_ofReal.continuousAt).mul (hkc x)
    · refine Eventually.of_forall (fun x => ?_)
      rw [norm_mul, norm_kz_real z hz]
      have := hb x (by simp)
      have hp : 0 ≤ 2 * z.im * ((x - z.re) ^ 2 + z.im ^ 2)⁻¹ := by
        have : 0 < (x - z.re) ^ 2 + z.im ^ 2 :=
          add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hz 2)
        positivity
      calc ‖G x‖ * (2 * z.im * ((x - z.re) ^ 2 + z.im ^ 2)⁻¹)
          ≤ C * (2 * z.im * ((x - z.re) ^ 2 + z.im ^ 2)⁻¹) := mul_le_mul_of_nonneg_right this hp
        _ = C * (2 * z.im) * ((x - z.re) ^ 2 + z.im ^ 2)⁻¹ := by ring
  have hbot := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  -- the three other edges vanish
  set R₁ := 2 * (|z.re| + z.im) + 1 with hR₁
  have hR₁pos : 0 < R₁ := by have := abs_nonneg z.re; linarith
  have hsmall : ∀ (p : ℝ → ℂ → ℂ) (α β : ℝ → ℝ) (L : ℝ),
      (∀ R, R₁ ≤ R → |β R - α R| ≤ L * R) →
      (∀ R, R₁ ≤ R → ∀ t ∈ Set.uIoc (α R) (β R), 0 ≤ (p R t).im ∧
        ((p R t).im = R ∨ |(p R t).re| = R)) → 0 ≤ L →
      Tendsto (fun R : ℝ => ∫ t in α R..β R, G (p R t) * kz z (p R t)) atTop (𝓝 0) := by
    intro p α β L hlen hpt hL
    have hlim : Tendsto (fun R : ℝ => (C * 8 * z.im * L) / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop R₁] with R hR
    have hRpos : 0 < R := lt_of_lt_of_le hR₁pos hR
    have hR' : 2 * (|z.re| + z.im) ≤ R := by linarith
    have hbd : ∀ t ∈ Set.uIoc (α R) (β R), ‖G (p R t) * kz z (p R t)‖ ≤ C * (8 * z.im / R ^ 2) := by
      intro t ht
      obtain ⟨h1, h2⟩ := hpt R hR t ht
      rw [norm_mul]
      exact mul_le_mul (hb _ h1) (norm_kz_le z _ hz R hR' h2) (norm_nonneg _) hC
    calc ‖∫ t in α R..β R, G (p R t) * kz z (p R t)‖
        ≤ C * (8 * z.im / R ^ 2) * |β R - α R| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ ≤ C * (8 * z.im / R ^ 2) * (L * R) :=
          mul_le_mul_of_nonneg_left (hlen R hR) (by positivity)
      _ = (C * 8 * z.im * L) / R := by field_simp
  have htop := hsmall (fun R x => (x : ℂ) + R * I) (fun R => -R) (fun R => R) 2
    (fun R hR => by
      have : 0 ≤ R := by linarith
      rw [abs_of_nonneg (by linarith)]; linarith)
    (fun R hR t ht => by
      have : 0 ≤ R := by linarith
      refine ⟨by simp [this], Or.inl (by simp)⟩) (by norm_num)
  have hright := hsmall (fun R y => (R : ℂ) + y * I) (fun _ => 0) (fun R => R) 1
    (fun R hR => by
      have : 0 ≤ R := by linarith
      rw [sub_zero, abs_of_nonneg this, one_mul])
    (fun R hR t ht => by
      have : 0 ≤ R := by linarith
      have ht' : 0 < t := by
        rw [Set.uIoc_of_le this] at ht
        exact ht.1
      refine ⟨by simp [ht'.le], Or.inr (by simp [abs_of_nonneg this])⟩) (by norm_num)
  have hleft := hsmall (fun R y => -(R : ℂ) + y * I) (fun _ => 0) (fun R => R) 1
    (fun R hR => by
      have : 0 ≤ R := by linarith
      rw [sub_zero, abs_of_nonneg this, one_mul])
    (fun R hR t ht => by
      have : 0 ≤ R := by linarith
      have ht' : 0 < t := by
        rw [Set.uIoc_of_le this] at ht
        exact ht.1
      refine ⟨by simp [ht'.le], Or.inr (by simp [abs_of_nonneg this])⟩) (by norm_num)
  have := ((hbot.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  simp only [sub_zero, smul_zero, add_zero] at this
  refine this.congr (fun R => ?_)
  simp only [RI, id]

/-- Poisson formula on the half plane for a bounded function holomorphic near the closed half plane. -/
lemma poisson (G : ℂ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hd : ∀ w : ℂ, 0 ≤ w.im → DifferentiableAt ℂ G w)
    (hb : ∀ w : ℂ, 0 ≤ w.im → ‖G w‖ ≤ C) (z : ℂ) (hz : 0 < z.im) :
    ∫ x : ℝ, G x * kz z x = G z * (2 * Real.pi * I) := by
  have h1 := RI_tendsto G C hC (fun w hw => (hd w hw).continuousAt) hb z hz
  have h2 := RI_tendsto (fun _ => (1 : ℂ)) 1 zero_le_one (fun _ _ => continuousAt_const)
    (fun _ _ => by simp) z hz
  have heq : ∀ᶠ R in atTop, RI (fun w => G w * kz z w) R =
      G z * RI (fun w => (fun _ => (1 : ℂ)) w * kz z w) R := by
    filter_upwards [eventually_gt_atTop (|z.re| + z.im)] with R hR
    have h0 := abs_nonneg z.re
    rw [RI_cauchy G hd z hz R (by linarith) (by linarith),
      RI_cauchy (fun _ => (1 : ℂ)) (fun _ _ => differentiableAt_const _) z hz R
        (by linarith) (by linarith), one_mul]
  have h3 := h2.const_mul (G z)
  have := tendsto_nhds_unique (h1.congr' heq) h3
  rw [this]
  simp only [one_mul]
  rw [integral_kz z hz]

/-- A holomorphic function with vanishing imaginary part on a connected open set is constant. -/
lemma const_of_im_zero (D : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hD : DifferentiableOn ℂ D U) (him : ∀ w ∈ U, (D w).im = 0) :
    ∀ x ∈ U, ∀ y ∈ U, D x = D y := by
  intro x hx y hy
  refine hU.is_const_of_deriv_eq_zero hU' hD (fun w hw => ?_) hx hy
  have hd : HasDerivAt D (deriv D w) w := (hD.differentiableAt (hU.mem_nhds hw)).hasDerivAt
  -- derivative along the real direction
  have hpath1 : HasDerivAt (fun u : ℂ => w + u) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add w
  have hpath2 : HasDerivAt (fun u : ℂ => w + u * I) I 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const I).const_add w
  have hc1 : HasDerivAt (fun u : ℂ => D (w + u)) (deriv D w * 1) 0 := by
    have : HasDerivAt D (deriv D w) (w + 0) := by simpa using hd
    exact this.comp (0 : ℂ) hpath1
  have hc2 : HasDerivAt (fun u : ℂ => D (w + u * I)) (deriv D w * I) 0 := by
    have : HasDerivAt D (deriv D w) (w + 0 * I) := by simpa using hd
    exact this.comp (0 : ℂ) hpath2
  have hr1 : HasDerivAt (fun t : ℝ => D (w + t)) (deriv D w * 1) 0 := by
    have := hc1.comp_ofReal (z := 0)
    simpa using this
  have hr2 : HasDerivAt (fun t : ℝ => D (w + t * I)) (deriv D w * I) 0 := by
    have := hc2.comp_ofReal (z := 0)
    simpa using this
  have hi1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hr1
  have hi2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hr2
  have hev1 : (fun t : ℝ => Complex.imCLM (D (w + t))) =ᶠ[𝓝 0] fun _ => 0 := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, w + t ∈ U := by
      have hcont : Continuous (fun t : ℝ => w + (t : ℂ)) := by fun_prop
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hw)
    filter_upwards [hmem] with t ht
    simp [him _ ht]
  have hev2 : (fun t : ℝ => Complex.imCLM (D (w + t * I))) =ᶠ[𝓝 0] fun _ => 0 := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, w + t * I ∈ U := by
      have hcont : Continuous (fun t : ℝ => w + (t : ℂ) * I) := by fun_prop
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hw)
    filter_upwards [hmem] with t ht
    simp [him _ ht]
  have z1 := hi1.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev1)
  have z2 := hi2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev2)
  simp at z1 z2
  apply Complex.ext
  · simpa using z2
  · simpa using z1

/-- The Cauchy-type transform of an integrable real density is holomorphic on the upper half plane. -/
lemma cauchy_differentiableAt (φ : ℝ → ℝ) (hφc : Continuous φ) (hφ : Integrable φ) (w₀ : ℂ)
    (hw₀ : 0 < w₀.im) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ t : ℝ, (φ t : ℂ) * ((t : ℂ) - w)⁻¹) w₀ := by
  set r := w₀.im / 2 with hr
  have hrpos : 0 < r := by positivity
  have hball : ∀ w ∈ Metric.ball w₀ r, r < w.im := by
    intro w hw
    have h1 := Complex.abs_im_le_norm (w - w₀)
    rw [Metric.mem_ball, dist_eq_norm] at hw
    rw [sub_im] at h1
    have := neg_abs_le (w.im - w₀.im)
    linarith
  have hne : ∀ w : ℂ, 0 < w.im → ∀ t : ℝ, (t : ℂ) - w ≠ 0 := by
    intro w hw t h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hnorm : ∀ w : ℂ, ∀ t : ℝ, w.im ≤ ‖(t : ℂ) - w‖ := by
    intro w t
    have := Complex.abs_im_le_norm ((t : ℂ) - w)
    simp at this
    linarith [le_abs_self w.im]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun w t => (φ t : ℂ) * ((t : ℂ) - w)⁻¹)
    (F' := fun w t => (φ t : ℂ) * (-(-1) / ((t : ℂ) - w) ^ 2))
    (x₀ := w₀) (s := Metric.ball w₀ r) (bound := fun t => |φ t| * (r ^ 2)⁻¹)
    (Metric.ball_mem_nhds w₀ hrpos)
    (by
      filter_upwards [Metric.ball_mem_nhds w₀ hrpos] with w hw
      apply Continuous.aestronglyMeasurable
      have hw' : 0 < w.im := lt_trans hrpos (hball w hw)
      exact (Complex.continuous_ofReal.comp hφc).mul
        (Continuous.inv₀ (by fun_prop) (hne w hw')))
    (by
      refine Integrable.mono' (hφ.norm.mul_const (w₀.im⁻¹)) ?_ ?_
      · apply Continuous.aestronglyMeasurable
        exact (Complex.continuous_ofReal.comp hφc).mul
          (Continuous.inv₀ (by fun_prop) (hne w₀ hw₀))
      · refine Eventually.of_forall (fun t => ?_)
        rw [norm_mul, norm_inv, Complex.norm_real]
        gcongr
        exact hnorm w₀ t)
    (by
      apply Continuous.aestronglyMeasurable
      exact (Complex.continuous_ofReal.comp hφc).mul
        (continuous_const.div (by fun_prop) (fun t => pow_ne_zero 2 (hne w₀ hw₀ t))))
    (by
      refine Eventually.of_forall (fun t w hw => ?_)
      have hw1 := hball w hw
      have hw' : 0 < w.im := lt_trans hrpos hw1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, neg_neg, norm_div, norm_one, norm_pow,
        one_div]
      gcongr
      exact (lt_of_lt_of_le hw1 (hnorm w t)).le)
    (hφ.abs.mul_const _)
    (by
      refine Eventually.of_forall (fun t w hw => ?_)
      have hw' : 0 < w.im := lt_trans hrpos (hball w hw)
      have := ((hasDerivAt_id w).const_sub (t : ℂ)).inv (hne w hw' t)
      exact this.const_mul (φ t : ℂ))
  exact key.2.differentiableAt

lemma lorentz_pos (z : ℂ) (hz : 0 < z.im) (x : ℝ) : 0 < (x - z.re) ^ 2 + z.im ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hz 2)

/-- Imaginary part of the Poisson formula. -/
lemma poisson_im (G : ℂ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hd : ∀ w : ℂ, 0 ≤ w.im → DifferentiableAt ℂ G w)
    (hb : ∀ w : ℂ, 0 ≤ w.im → ‖G w‖ ≤ C) (z : ℂ) (hz : 0 < z.im) :
    (G z).im = ∫ x : ℝ, (G x).im / Real.pi * (z.im * ((x - z.re) ^ 2 + z.im ^ 2)⁻¹) := by
  set L : ℝ → ℝ := fun x => ((x - z.re) ^ 2 + z.im ^ 2)⁻¹ with hL
  have hGc : Continuous (fun x : ℝ => G x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hd x (by simp)).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hLc : Continuous L := by
    simp only [hL]
    exact Continuous.inv₀ (by fun_prop) (fun x => (lorentz_pos z hz x).ne')
  have hint : Integrable (fun x : ℝ => G x * (L x : ℂ)) := by
    refine Integrable.mono' ((integrable_lorentz z.re z.im hz).const_mul C) ?_ ?_
    · exact (hGc.mul (Complex.continuous_ofReal.comp hLc)).aestronglyMeasurable
    · refine Eventually.of_forall (fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (lorentz_pos z hz x))]
      exact mul_le_mul_of_nonneg_right (hb x (by simp)) (inv_pos.2 (lorentz_pos z hz x)).le
  have hP := poisson G C hC hd hb z hz
  simp_rw [kz_real] at hP
  have h1 : ∫ x : ℝ, G x * (2 * z.im * I * (L x : ℂ)) = (2 * z.im * I) * ∫ x : ℝ, G x * (L x : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  rw [h1] at hP
  have hne : (2 * (z.im : ℂ) * I) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    simp [this, Complex.I_ne_zero]
  have hJ : ∫ x : ℝ, G x * (L x : ℂ) = G z * ((Real.pi / z.im : ℝ) : ℂ) := by
    have h2 : ∫ x : ℝ, G x * (L x : ℂ) = G z * (2 * Real.pi * I) / (2 * z.im * I) :=
      eq_div_of_mul_eq hne (by rw [mul_comm]; exact hP)
    rw [h2]
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    push_cast
    field_simp
  have hJim := congrArg Complex.im hJ
  have hcomm := integral_im (𝕜 := ℂ) hint
  simp only [RCLike.im_to_complex] at hcomm
  rw [← hcomm] at hJim
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    add_zero] at hJim
  -- hJim : ∫ (G x).im * L x = (G z).im * (π / y)
  have h3 : ∫ x : ℝ, (G x).im / Real.pi * (z.im * L x) =
      z.im / Real.pi * ∫ x : ℝ, (G x).im * L x := by
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  simp only [hL] at h3 hJim ⊢
  rw [h3, hJim]
  field_simp

open TeschlQM.Herglotz in
/-- H1: representation of the shifted Herglotz function. -/
theorem herglotz_shift_repr (F : ℂ → ℂ) (hF : IsHerglotz F) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ M / z.im) (ε : ℝ) (hε : 0 < ε) :
    (volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal ((F ((x : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi))) Set.univ
        ≤ ENNReal.ofReal M ∧
      ∀ z : ℂ, 0 < z.im → F (z + (ε : ℂ) * Complex.I) =
        borelTransform (volume.withDensity (fun x : ℝ =>
          ENNReal.ofReal ((F ((x : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi))) z := by
  set G : ℂ → ℂ := fun w => F (w + (ε : ℂ) * I) with hGdef
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hshift : ∀ w : ℂ, (w + (ε : ℂ) * I).im = w.im + ε := by intro w; simp
  have hM0 : 0 ≤ M := by
    have h := hM I (by simp)
    simp only [Complex.I_im, div_one] at h
    exact le_trans (norm_nonneg _) h
  have hGd : ∀ w : ℂ, 0 ≤ w.im → DifferentiableAt ℂ G w := by
    intro w hw
    have hpos : 0 < (w + (ε : ℂ) * I).im := by rw [hshift]; linarith
    have := hF.1.differentiableAt (hopen.mem_nhds hpos)
    exact this.comp w (differentiableAt_id.add_const _)
  have hGb' : ∀ w : ℂ, 0 ≤ w.im → ‖G w‖ ≤ M / (w.im + ε) := by
    intro w hw
    have := hM (w + (ε : ℂ) * I) (by rw [hshift]; linarith)
    rwa [hshift] at this
  have hGb : ∀ w : ℂ, 0 ≤ w.im → ‖G w‖ ≤ M / ε := by
    intro w hw
    exact (hGb' w hw).trans (div_le_div_of_nonneg_left hM0 hε (by linarith))
  have hGim : ∀ w : ℂ, 0 ≤ w.im → 0 < (G w).im := by
    intro w hw
    exact hF.2 _ (by rw [hshift]; linarith)
  have hGc : Continuous (fun x : ℝ => G x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hGd x (by simp)).continuousAt.comp Complex.continuous_ofReal.continuousAt
  set φ : ℝ → ℝ := fun x => (G x).im / Real.pi with hφdef
  have hφc : Continuous φ := (Complex.continuous_im.comp hGc).div_const _
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => div_nonneg (hGim x (by simp)).le Real.pi_pos.le
  have hCε : 0 ≤ M / ε := div_nonneg hM0 hε.le
  have hPim : ∀ z : ℂ, 0 < z.im →
      (G z).im = ∫ x : ℝ, φ x * (z.im * ((x - z.re) ^ 2 + z.im ^ 2)⁻¹) :=
    fun z hz => poisson_im G (M / ε) hCε hGd hGb z hz
  -- weights `v n x = n^2/(x^2+n^2)`
  set v : ℕ → ℝ → ℝ := fun n x => (n : ℝ) ^ 2 * (x ^ 2 + (n : ℝ) ^ 2)⁻¹ with hv
  have hden : ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x ^ 2 + (n : ℝ) ^ 2 := by
    intro n hn x
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hnpos 2)
  have hφb : ∀ x, φ x ≤ M / ε / Real.pi := fun x =>
    div_le_div_of_nonneg_right ((le_abs_self _).trans ((Complex.abs_im_le_norm _).trans
      (hGb x (by simp)))) Real.pi_pos.le
  have hv_int : ∀ n : ℕ, 1 ≤ n → Integrable (fun x : ℝ => φ x * v n x) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    refine Integrable.mono' (((integrable_lorentz 0 n hnpos).const_mul ((n : ℝ) ^ 2)).const_mul
      (M / ε / Real.pi)) ?_ ?_
    · exact (hφc.mul (continuous_const.mul (Continuous.inv₀ (by fun_prop)
        (fun x => (hden n hn x).ne')))).aestronglyMeasurable
    · refine Eventually.of_forall (fun x => ?_)
      have hp := hden n hn x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφ0 x) (by positivity))]
      calc φ x * v n x ≤ M / ε / Real.pi * v n x :=
            mul_le_mul_of_nonneg_right (hφb x) (by positivity)
        _ = M / ε / Real.pi * ((n : ℝ) ^ 2 * ((x - 0) ^ 2 + (n : ℝ) ^ 2)⁻¹) := by
            simp [hv]
  have hv_le : ∀ n : ℕ, 1 ≤ n → ∫ x : ℝ, φ x * v n x ≤ M := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hz : 0 < ((n : ℂ) * I).im := by simpa using hnpos
    have h1 := hPim ((n : ℂ) * I) hz
    simp only [mul_im, natCast_re, I_im, mul_one, natCast_im, I_re, mul_zero, add_zero,
      mul_re, sub_zero, zero_mul] at h1
    have h2 : (G ((n : ℂ) * I)).im ≤ M / n := by
      have := hGb' ((n : ℂ) * I) hz.le
      simp only [mul_im, natCast_re, I_im, mul_one, natCast_im, I_re, mul_zero,
        add_zero] at this
      calc (G ((n : ℂ) * I)).im ≤ ‖G ((n : ℂ) * I)‖ :=
            (le_abs_self _).trans (Complex.abs_im_le_norm _)
        _ ≤ M / (n + ε) := this
        _ ≤ M / n := div_le_div_of_nonneg_left hM0 hnpos (by linarith)
    have h3 : ∫ x : ℝ, φ x * v n x = n * ∫ x : ℝ, φ x * ((n : ℝ) * (x ^ 2 + (n : ℝ) ^ 2)⁻¹) := by
      rw [← integral_const_mul]
      congr 1
      ext x
      simp only [hv]
      ring
    rw [h3, ← h1]
    calc (n : ℝ) * (G ((n : ℂ) * I)).im ≤ n * (M / n) :=
          mul_le_mul_of_nonneg_left h2 hnpos.le
      _ = M := by field_simp
  -- Fatou: total mass `≤ M`
  have hv_lim : ∀ x : ℝ, Tendsto (fun n : ℕ => v n x) atTop (𝓝 1) := by
    intro x
    have h0 : Tendsto (fun n : ℕ => x ^ 2 * ((n : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp
        tendsto_natCast_atTop_atTop)).const_mul (x ^ 2)
      simpa using this
    have h1 : Tendsto (fun n : ℕ => (1 + x ^ 2 * ((n : ℝ) ^ 2)⁻¹)⁻¹) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add h0
      have := this.inv₀ (by norm_num)
      simpa using this
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hv]
    field_simp
    ring
  have hlint : ∫⁻ x : ℝ, ENNReal.ofReal (φ x) ≤ ENNReal.ofReal M := by
    have hmeas : ∀ n : ℕ, Measurable (fun x : ℝ => ENNReal.ofReal (φ x * v n x)) := by
      intro n
      exact (hφc.measurable.mul (by simp only [hv]; fun_prop)).ennreal_ofReal
    have hf := lintegral_liminf_le (μ := (volume : Measure ℝ)) (u := atTop) hmeas
    have hl : ∀ x : ℝ, liminf (fun n : ℕ => ENNReal.ofReal (φ x * v n x)) atTop =
        ENNReal.ofReal (φ x) := by
      intro x
      have := ((hv_lim x).const_mul (φ x))
      rw [mul_one] at this
      exact (ENNReal.tendsto_ofReal this).liminf_eq
    simp only [hl] at hf
    refine hf.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hv_int n hn)
      (ae_of_all _ (fun x => mul_nonneg (hφ0 x) (by simp only [hv]; positivity)))]
    exact ENNReal.ofReal_le_ofReal (hv_le n hn)
  have hφint : Integrable φ :=
    (lintegral_ofReal_ne_top_iff_integrable hφc.aestronglyMeasurable (ae_of_all _ hφ0)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlint)
  refine ⟨?_, ?_⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hlint
  intro z hz
  set Bf : ℂ → ℂ := fun w => ∫ t : ℝ, (φ t : ℂ) * ((t : ℂ) - w)⁻¹ with hBf
  have hB : borelTransform (volume.withDensity (fun x : ℝ => ENNReal.ofReal (φ x))) z = Bf z := by
    unfold borelTransform
    rw [integral_withDensity_eq_integral_toReal_smul hφc.measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    congr 1
    ext t
    rw [ENNReal.toReal_ofReal (hφ0 t), Complex.real_smul]
  have hnorm_le : ∀ w : ℂ, ∀ t : ℝ, w.im ≤ ‖(t : ℂ) - w‖ := by
    intro w t
    have := Complex.abs_im_le_norm ((t : ℂ) - w)
    simp at this
    linarith [le_abs_self w.im]
  have hbnd : ∀ w : ℂ, 0 < w.im → ∀ t : ℝ, ‖(φ t : ℂ) * ((t : ℂ) - w)⁻¹‖ ≤ φ t * w.im⁻¹ := by
    intro w hw t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 t), norm_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hw (hnorm_le w t)) (hφ0 t)
  have hBint : ∀ w : ℂ, 0 < w.im → Integrable (fun t : ℝ => (φ t : ℂ) * ((t : ℂ) - w)⁻¹) := by
    intro w hw
    refine Integrable.mono' (hφint.mul_const _) ?_ (Eventually.of_forall (hbnd w hw))
    have hne : ∀ t : ℝ, (t : ℂ) - w ≠ 0 := by
      intro t h0
      have := congrArg Complex.im h0
      simp at this
      linarith
    exact ((Complex.continuous_ofReal.comp hφc).mul
      (Continuous.inv₀ (by fun_prop) hne)).aestronglyMeasurable
  have hBim : ∀ w : ℂ, 0 < w.im →
      (Bf w).im = ∫ x : ℝ, φ x * (w.im * ((x - w.re) ^ 2 + w.im ^ 2)⁻¹) := by
    intro w hw
    have hcomm := integral_im (𝕜 := ℂ) (hBint w hw)
    simp only [RCLike.im_to_complex] at hcomm
    simp only [hBf]
    rw [← hcomm]
    congr 1
    ext x
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.inv_im, Complex.normSq_apply]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im]
    ring
  set U : Set ℂ := {w : ℂ | 0 < w.im} with hU
  have hDim : ∀ w ∈ U, (G w - Bf w).im = 0 := by
    intro w hw
    rw [Complex.sub_im, hPim w hw, hBim w hw, sub_self]
  have hDdiff : DifferentiableOn ℂ (fun w => G w - Bf w) U := by
    intro w hw
    exact ((hGd w (le_of_lt hw)).sub (cauchy_differentiableAt φ hφc hφint w hw)).differentiableWithinAt
  have hconst := const_of_im_zero (fun w => G w - Bf w) U hopen
    (convex_halfSpace_im_gt 0).isPreconnected hDdiff hDim
  set K := M + ∫ t : ℝ, φ t with hK
  have hsmall : ∀ n : ℕ, 1 ≤ n → ‖G z - Bf z‖ ≤ K / n := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hz' : 0 < ((n : ℂ) * I).im := by simpa using hnpos
    have hc := hconst z hz ((n : ℂ) * I) hz'
    rw [hc]
    have hnI : ((n : ℂ) * I).im = n := by simp
    have h1 : ‖G ((n : ℂ) * I)‖ ≤ M / n := by
      have := hGb' ((n : ℂ) * I) hz'.le
      rw [hnI] at this
      exact this.trans (div_le_div_of_nonneg_left hM0 hnpos (by linarith))
    have h2 : ‖Bf ((n : ℂ) * I)‖ ≤ (∫ t : ℝ, φ t) / n := by
      have := norm_integral_le_of_norm_le (hφint.mul_const ((n : ℝ)⁻¹))
        (Eventually.of_forall (fun t => (hnI ▸ hbnd ((n : ℂ) * I) hz' t)))
      rw [integral_mul_const] at this
      simpa [div_eq_mul_inv, hBf] using this
    calc ‖G ((n : ℂ) * I) - Bf ((n : ℂ) * I)‖
        ≤ ‖G ((n : ℂ) * I)‖ + ‖Bf ((n : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ M / n + (∫ t : ℝ, φ t) / n := add_le_add h1 h2
      _ = K / n := by rw [hK, add_div]
  have hzero : ‖G z - Bf z‖ ≤ 0 := by
    refine ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat K) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hsmall n hn
  have hGB : G z = Bf z := sub_eq_zero.1 (norm_le_zero_iff.1 hzero)
  rw [hB]
  exact hGB


/-- Extension of a function on `ℝ` to `EReal` by `0` at `±∞`. -/
noncomputable def ext0 (g : ℝ → ℂ) : EReal → ℂ := fun x =>
  if x = ⊤ ∨ x = ⊥ then 0 else g x.toReal

lemma ext0_coe (g : ℝ → ℂ) (x : ℝ) : ext0 g x = g x := by
  simp [ext0]

lemma ext0_top (g : ℝ → ℂ) : ext0 g ⊤ = 0 := by simp [ext0]

lemma ext0_bot (g : ℝ → ℂ) : ext0 g ⊥ = 0 := by simp [ext0]

lemma continuous_ext0 (g : ℝ → ℂ) (hg : Continuous g)
    (h0 : Tendsto g (cocompact ℝ) (𝓝 0)) : Continuous (ext0 g) := by
  rw [continuous_iff_continuousAt]
  intro x
  induction x using EReal.rec with
  | bot =>
    have hb : Tendsto g atBot (𝓝 0) :=
      h0.mono_left atBot_le_cocompact
    show Tendsto (ext0 g) (𝓝 ⊥) (𝓝 (ext0 g ⊥))
    rw [ext0_bot, EReal.nhds_bot_basis.tendsto_iff Metric.nhds_basis_ball]
    intro e he
    obtain ⟨a, -, ha⟩ := (atBot_basis.tendsto_iff Metric.nhds_basis_ball).1 hb e he
    refine ⟨a, trivial, fun y hy => ?_⟩
    induction y using EReal.rec with
    | bot => rw [ext0_bot]; exact Metric.mem_ball_self he
    | top => exact absurd hy (by simp)
    | coe r =>
      rw [ext0_coe]
      exact ha r (le_of_lt (EReal.coe_lt_coe_iff.1 hy))
  | top =>
    have hb : Tendsto g atTop (𝓝 0) :=
      h0.mono_left atTop_le_cocompact
    show Tendsto (ext0 g) (𝓝 ⊤) (𝓝 (ext0 g ⊤))
    rw [ext0_top, EReal.nhds_top_basis.tendsto_iff Metric.nhds_basis_ball]
    intro e he
    obtain ⟨a, -, ha⟩ := (atTop_basis.tendsto_iff Metric.nhds_basis_ball).1 hb e he
    refine ⟨a, trivial, fun y hy => ?_⟩
    induction y using EReal.rec with
    | top => rw [ext0_top]; exact Metric.mem_ball_self he
    | bot => exact absurd hy (by simp)
    | coe r =>
      rw [ext0_coe]
      exact ha r (le_of_lt (EReal.coe_lt_coe_iff.1 hy))
  | coe r =>
    have hc : ext0 g ∘ ((↑) : ℝ → EReal) = g := funext (ext0_coe g)
    rw [← EReal.isOpenEmbedding_coe.continuousAt_iff, hc]
    exact hg.continuousAt

/-- H2: Helly selection via Prokhorov compactness on `EReal`. -/
theorem exists_vague_clusterPt (μ : ℝ → Measure ℝ) (M : ℝ)
    (hμ : ∀ ε : ℝ, 0 < ε → μ ε Set.univ ≤ ENNReal.ofReal M) :
    ∃ ν : Measure ℝ, ν Set.univ ≤ ENNReal.ofReal M ∧ ∃ 𝓕 : Filter ℝ, 𝓕.NeBot ∧
      𝓕 ≤ 𝓝[>] (0 : ℝ) ∧
      ∀ g : ℝ → ℂ, Continuous g → Tendsto g (Filter.cocompact ℝ) (𝓝 0) →
        Tendsto (fun ε => ∫ x, g x ∂(μ ε)) 𝓕 (𝓝 (∫ x, g x ∂ν)) := by
  classical
  have hemb : MeasurableEmbedding ((↑) : ℝ → EReal) :=
    EReal.isOpenEmbedding_coe.measurableEmbedding
  let μ' : ℝ → Measure ℝ := fun ε => if 0 < ε then μ ε else 0
  have hle : ∀ ε, ((μ' ε).map ((↑) : ℝ → EReal)) Set.univ ≤ ENNReal.ofReal M := by
    intro ε
    rw [Measure.map_apply measurable_coe_real_ereal MeasurableSet.univ, Set.preimage_univ]
    by_cases h : 0 < ε
    · simp only [μ', if_pos h]; exact hμ ε h
    · simp [μ', h]
  have hfin : ∀ ε, IsFiniteMeasure ((μ' ε).map ((↑) : ℝ → EReal)) := fun ε =>
    ⟨lt_of_le_of_lt (hle ε) ENNReal.ofReal_lt_top⟩
  let μt : ℝ → FiniteMeasure EReal := fun ε => ⟨(μ' ε).map ((↑) : ℝ → EReal), hfin ε⟩
  have hmass : ∀ ε, (μt ε).mass ≤ M.toNNReal := by
    intro ε
    have h1 : ((μt ε).mass : ENNReal) ≤ ENNReal.ofReal M := by
      rw [FiniteMeasure.ennreal_mass]; exact hle ε
    rw [ENNReal.ofReal] at h1
    exact_mod_cast h1
  have hK := isCompact_setOfPred_finiteMeasure_le_of_compactSpace EReal M.toNNReal
  obtain ⟨ν, hνK, hν⟩ := hK (f := map μt (𝓝[>] (0 : ℝ)))
    (by
      rw [le_principal_iff, mem_map]
      exact Filter.univ_mem' (fun ε => hmass ε))
  obtain ⟨U, hU, hUt⟩ := mapClusterPt_iff_ultrafilter.1 hν
  refine ⟨(ν : Measure EReal).comap ((↑) : ℝ → EReal), ?_, (U : Filter ℝ), U.neBot, hU, ?_⟩
  · rw [hemb.comap_apply, Set.image_univ]
    calc (ν : Measure EReal) (Set.range ((↑) : ℝ → EReal))
        ≤ (ν : Measure EReal) Set.univ := measure_mono (Set.subset_univ _)
      _ = (ν.mass : ENNReal) := FiniteMeasure.ennreal_mass.symm
      _ ≤ ENNReal.ofReal M := by
          rw [ENNReal.ofReal]; exact_mod_cast (hνK : ν.mass ≤ M.toNNReal)
  · intro g hg h0
    let G : EReal →ᵇ ℂ :=
      BoundedContinuousFunction.mkOfCompact ⟨ext0 g, continuous_ext0 g hg h0⟩
    have hlim := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hUt G
    have e1 : ∀ᶠ ε in (U : Filter ℝ),
        ∫ x, G x ∂(μt ε : Measure EReal) = ∫ x, g x ∂(μ ε) := by
      filter_upwards [hU self_mem_nhdsWithin] with ε hε
      show ∫ x, ext0 g x ∂((μ' ε).map ((↑) : ℝ → EReal)) = _
      rw [hemb.integral_map]
      simp only [μ', if_pos (show (0 : ℝ) < ε from hε), ext0_coe]
    have e2 : ∫ x, G x ∂(ν : Measure EReal) =
        ∫ x, g x ∂((ν : Measure EReal).comap ((↑) : ℝ → EReal)) := by
      symm
      calc ∫ x, g x ∂((ν : Measure EReal).comap ((↑) : ℝ → EReal))
          = ∫ x, ext0 g (x : EReal) ∂((ν : Measure EReal).comap ((↑) : ℝ → EReal)) := by
            simp only [ext0_coe]
        _ = ∫ y, ext0 g y ∂(((ν : Measure EReal).comap ((↑) : ℝ → EReal)).map
              ((↑) : ℝ → EReal)) := (hemb.integral_map _).symm
        _ = ∫ y, ext0 g y ∂((ν : Measure EReal).restrict (Set.range ((↑) : ℝ → EReal))) := by
            rw [hemb.map_comap]
        _ = ∫ y, ext0 g y ∂(ν : Measure EReal) := by
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro y hy
            induction y using EReal.rec with
            | bot => exact ext0_bot g
            | top => exact ext0_top g
            | coe r => exact absurd (Set.mem_range_self r) hy
    rw [e2] at hlim
    exact hlim.congr' e1

lemma tendsto_kernel_cocompact (z : ℂ) :
    Tendsto (fun x : ℝ => ((x : ℂ) - z)⁻¹) (cocompact ℝ) (𝓝 0) := by
  have hn : Tendsto (fun x : ℝ => ‖x‖ - ‖z‖) (cocompact ℝ) atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_norm_cocompact_atTop
  have hn' : Tendsto (fun x : ℝ => ‖(x : ℂ) - z‖) (cocompact ℝ) atTop := by
    refine tendsto_atTop_mono (fun x => ?_) hn
    have := norm_sub_norm_le (x : ℂ) z
    rwa [Complex.norm_real] at this
  exact tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 hn')

end HerglotzRepr1b26

open MeasureTheory TeschlQM.Herglotz in
theorem solution (F : ℂ → ℂ) (hF : IsHerglotz F) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ M / z.im) :
    ∃ μ : Measure ℝ, μ Set.univ ≤ ENNReal.ofReal M ∧
      ∀ z : ℂ, 0 < z.im → F z = borelTransform μ z := by
  let μ : ℝ → Measure ℝ := fun ε => volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal ((F ((x : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi))
  obtain ⟨ν, hν, 𝓕, h𝓕, h𝓕le, hlim⟩ := HerglotzRepr1b26.exists_vague_clusterPt μ M
    (fun ε hε => (HerglotzRepr1b26.herglotz_shift_repr F hF M hM ε hε).1)
  refine ⟨ν, hν, fun z hz => ?_⟩
  have hg : Continuous (fun x : ℝ => ((x : ℂ) - z)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) (fun x h => ?_)
    have := congrArg Complex.im h
    simp at this
    linarith
  have h1 := hlim _ hg (HerglotzRepr1b26.tendsto_kernel_cocompact z)
  have h2 : Tendsto (fun ε : ℝ => F (z + (ε : ℂ) * Complex.I)) 𝓕 (𝓝 (F z)) := by
    have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have hcont : ContinuousAt F z :=
      (hF.1.differentiableAt (hopen.mem_nhds hz)).continuousAt
    have ht : Tendsto (fun ε : ℝ => z + (ε : ℂ) * Complex.I) (𝓝 0) (𝓝 z) := by
      have hc : Continuous (fun ε : ℝ => z + (ε : ℂ) * Complex.I) := by fun_prop
      simpa using hc.tendsto 0
    exact (hcont.tendsto.comp ht).mono_left (h𝓕le.trans nhdsWithin_le_nhds)
  have h3 : ∀ᶠ ε : ℝ in 𝓕, F (z + (ε : ℂ) * Complex.I) = ∫ x, ((x : ℂ) - z)⁻¹ ∂(μ ε) := by
    filter_upwards [h𝓕le self_mem_nhdsWithin] with ε hε
    exact (HerglotzRepr1b26.herglotz_shift_repr F hF M hM ε hε).2 z hz
  exact tendsto_nhds_unique (h2.congr' h3) h1

