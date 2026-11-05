-- Prove2me | solution 1 for SpikedWishart.SoftEdge.J_conn_piece
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:48:49.924631+00:00
-- url     : https://prove2.me/submissions/83e4e3f7-f133-4076-9d31-6f8a55037ae7

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option linter.all false
set_option Elab.async false

open Complex

namespace P31J2
open SpikedWishart.SoftEdge MeasureTheory


/-- `‖e^x - 1‖ ≤ 2‖x‖ e^{‖x‖}` for every complex `x`. -/
theorem norm_exp_sub_one_le' (x : ℂ) : ‖exp x - 1‖ ≤ 2 * ‖x‖ * Real.exp ‖x‖ := by
  have h1 : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg x)
  rcases le_total ‖x‖ 1 with hx | hx
  · have := Complex.norm_exp_sub_one_le hx
    have h2 : 0 ≤ 2 * ‖x‖ := by positivity
    nlinarith
  · have h3 : ‖exp x‖ ≤ Real.exp ‖x‖ := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (Complex.re_le_norm x)
    calc ‖exp x - 1‖ ≤ ‖exp x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp ‖x‖ + 1 := by rw [norm_one]; linarith only [h3]
      _ ≤ 2 * ‖x‖ * Real.exp ‖x‖ := by nlinarith

theorem cubic_bound (A B : ℝ) : ∃ D : ℝ, ∀ t : ℝ, 0 ≤ t → A * t + B * t ^ 2 - t ^ 3 / 3 ≤ D := by
  have hL0 : 0 ≤ |A| + |B| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨(|A| + |B|) + 9 * (|A| + |B|) ^ 3, fun t ht => ?_⟩
  have hA : A * t ≤ |A| * t := mul_le_mul_of_nonneg_right (le_abs_self A) ht
  have hB : B * t ^ 2 ≤ |B| * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg t)
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
  have hL3 : 0 ≤ (|A| + |B|) ^ 3 := pow_nonneg hL0 3
  rcases le_total t 1 with h1 | h1
  · have h1A : |A| * t ≤ |A| := mul_le_of_le_one_right (abs_nonneg A) h1
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have h1B : |B| * t ^ 2 ≤ |B| := mul_le_of_le_one_right (abs_nonneg B) ht2
    linarith only [hA, hB, ht3, hL3, h1A, h1B]
  · have hAt : |A| * t ≤ |A| * t ^ 2 := by
      have : t ≤ t ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (abs_nonneg A)
    rcases le_total t (3 * (|A| + |B|)) with h2 | h2
    · have h9 : t ^ 2 ≤ 9 * (|A| + |B|) ^ 2 := by nlinarith
      have h9' := mul_le_mul_of_nonneg_left h9 hL0
      nlinarith
    · have hneg := mul_nonneg (sq_nonneg t) (sub_nonneg.2 h2)
      nlinarith

theorem re_cube (a : ℂ) : (a ^ 3).re = a.re ^ 3 - 3 * a.re * a.im ^ 2 := by
  rw [show a ^ 3 = a * a * a by ring, Complex.mul_re, Complex.mul_re, Complex.mul_im]; ring


/-- Inverting a ratio close to `1`: `‖w - 1‖ ≤ η ≤ 1/2` gives `‖w⁻¹ - 1‖ ≤ 2η`. -/
theorem inv_ratio (w : ℂ) (η : ℝ) (h : ‖w - 1‖ ≤ η) (hη : η ≤ 1 / 2) :
    w ≠ 0 ∧ ‖w⁻¹ - 1‖ ≤ 2 * η := by
  have h1 := norm_le_norm_add_norm_sub' (1 : ℂ) w
  rw [norm_one, norm_sub_rev] at h1
  have hw : 1 / 2 ≤ ‖w‖ := by linarith only [h, hη, h1]
  have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; linarith only [hw]
  refine ⟨hw0, ?_⟩
  have e : w⁻¹ - 1 = -((w - 1) * w⁻¹) := by rw [sub_mul, mul_inv_cancel₀ hw0, one_mul]; ring
  rw [e, norm_neg, norm_mul, norm_inv]
  have h2 : ‖w‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith only [hw]) (by norm_num)]; linarith only [hw]
  calc ‖w - 1‖ * ‖w‖⁻¹ ≤ η * 2 := mul_le_mul h h2 (by positivity) ((norm_nonneg _).trans h)
    _ = 2 * η := by ring

theorem interval_exp_bound (Φ : ℝ → ℂ) (T B : ℝ) (w : ℂ) (hT : 0 ≤ T) (hw : ‖w‖ = 1)
    (h : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → ‖Φ τ‖ ≤ B * Real.exp (-τ)) (hB : 0 ≤ B) :
    ‖∫ τ in (0 : ℝ)..T, Φ τ * w‖ ≤ B := by
  have h1 : ‖∫ τ in (0 : ℝ)..T, Φ τ * w‖ ≤ ∫ τ in (0 : ℝ)..T, B * Real.exp (-τ) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT
    · refine Filter.Eventually.of_forall (fun τ hτ => ?_)
      rw [norm_mul, hw, mul_one]; exact h τ hτ.1.le hτ.2
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h2 : ∫ τ in (0 : ℝ)..T, B * Real.exp (-τ) = B * (1 - Real.exp (-T)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg (fun x => Real.exp x), integral_exp]; simp
  have h3 : 0 < Real.exp (-T) := Real.exp_pos _
  rw [h2] at h1; nlinarith



/-- Change of variables `τ = σ t` on a ray of the z-contour. -/
theorem ray_rescale (H : ℂ → ℂ) (p c σ δ : ℝ) (w : ℂ) (hσ : 0 < σ) :
    (∫ t in (0 : ℝ)..δ, H (((p + c / σ : ℝ) : ℂ) + (t : ℂ) * w) * w) =
      ((σ⁻¹ : ℝ) : ℂ) * ∫ τ in (0 : ℝ)..(σ * δ),
        H ((p : ℂ) + ((c : ℂ) + (τ : ℂ) * w) / (σ : ℂ)) * w := by
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have key : ∀ t : ℝ, H (((p + c / σ : ℝ) : ℂ) + (t : ℂ) * w) * w =
      (fun τ : ℝ => H ((p : ℂ) + ((c : ℂ) + (τ : ℂ) * w) / (σ : ℂ)) * w) (σ * t) := by
    intro t
    simp only
    congr 2
    push_cast; field_simp; ring
  calc (∫ t in (0 : ℝ)..δ, H (((p + c / σ : ℝ) : ℂ) + (t : ℂ) * w) * w)
      = ∫ t in (0 : ℝ)..δ,
          (fun τ : ℝ => H ((p : ℂ) + ((c : ℂ) + (τ : ℂ) * w) / (σ : ℂ)) * w) (σ * t) := by
        congr 1; funext t; exact key t
    _ = _ := by
        rw [intervalIntegral.integral_comp_mul_left
          (fun τ : ℝ => H ((p : ℂ) + ((c : ℂ) + (τ : ℂ) * w) / (σ : ℂ)) * w) hσ.ne', mul_zero,
          Complex.real_smul]



/-- Taylor input in the rescaled variable: `‖M(f(p_c + a/σ) - f(p_c)) - a³/3‖ ≤ C₁ ‖a‖⁴ / m`. -/
theorem F_scale (γ q m σ C₁ : ℝ) (M : ℕ) (a : ℂ) (hm : 0 < m) (hm3 : m ^ 3 = (M : ℝ))
    (hν : 1 ≤ nu γ) (hσ : σ = nu γ * m) (hC : 0 ≤ C₁)
    (hT : ‖fFn γ q ((pc γ : ℂ) + a / σ) - fFn γ q (pc γ) -
        ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((pc γ : ℂ) + a / σ - pc γ) ^ 3‖ ≤
        C₁ * ‖(pc γ : ℂ) + a / σ - pc γ‖ ^ 4) :
    ‖(M : ℂ) * (fFn γ q ((pc γ : ℂ) + a / σ) - fFn γ q (pc γ)) - a ^ 3 / 3‖ ≤
      C₁ * (1 / m) * ‖a‖ ^ 4 := by
  have hν0 : 0 < nu γ := by linarith only [hν]
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  rw [add_sub_cancel_left] at hT
  have hMc : (M : ℂ) = ((m ^ 3 : ℝ) : ℂ) := by rw [hm3]; norm_cast
  have hid : (M : ℂ) * (fFn γ q ((pc γ : ℂ) + a / σ) - fFn γ q (pc γ)) - a ^ 3 / 3 =
      (M : ℂ) * (fFn γ q ((pc γ : ℂ) + a / σ) - fFn γ q (pc γ) -
        ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (a / σ) ^ 3) := by
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hn0 : (nu γ : ℂ) ≠ 0 := by exact_mod_cast hν0.ne'
    rw [hMc, hσ]; push_cast
    field_simp
  rw [hid, norm_mul, Complex.norm_natCast]
  have hnorm : ‖a / (σ : ℂ)‖ = ‖a‖ / σ := by
    rw [norm_div, norm_real, Real.norm_of_nonneg hσ0.le]
  rw [hnorm] at hT
  have hMm : (M : ℝ) * (C₁ * (‖a‖ / σ) ^ 4) = C₁ * (1 / m) * ‖a‖ ^ 4 * (1 / nu γ ^ 4) := by
    rw [← hm3, hσ]; field_simp
  have hν4 : 1 / nu γ ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hν
  have hX : 0 ≤ C₁ * (1 / m) * ‖a‖ ^ 4 := by positivity
  calc (M : ℝ) * ‖fFn γ q ((pc γ : ℂ) + a / σ) - fFn γ q (pc γ) -
        ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (a / σ) ^ 3‖ ≤ (M : ℝ) * (C₁ * (‖a‖ / σ) ^ 4) :=
        mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg _)
    _ = C₁ * (1 / m) * ‖a‖ ^ 4 * (1 / nu γ ^ 4) := hMm
    _ ≤ C₁ * (1 / m) * ‖a‖ ^ 4 := mul_le_of_le_one_right hX hν4

/-- `g`-ratio input in the rescaled variable. -/
theorem G_scale (γ K₂ m σ : ℝ) (G a : ℂ) (hm : 0 < m) (hν : 1 ≤ nu γ) (hσ : σ = nu γ * m)
    (hK : 0 ≤ K₂) (hG : ‖G - 1‖ ≤ K₂ * ‖(pc γ : ℂ) + a / σ - pc γ‖) :
    ‖G - 1‖ ≤ K₂ * (1 / m) * ‖a‖ := by
  have hσ0 : 0 < σ := by rw [hσ]; nlinarith
  rw [add_sub_cancel_left, norm_div, norm_real, Real.norm_of_nonneg hσ0.le] at hG
  refine hG.trans ?_
  have h1 : ‖a‖ / σ ≤ (1 / m) * ‖a‖ := by
    rw [hσ, div_le_iff₀ (by positivity)]
    have : (1 / m) * ‖a‖ * (nu γ * m) = nu γ * ‖a‖ := by field_simp
    rw [this]; nlinarith [norm_nonneg a]
  calc K₂ * (‖a‖ / σ) ≤ K₂ * ((1 / m) * ‖a‖) := mul_le_mul_of_nonneg_left h1 hK
    _ = K₂ * (1 / m) * ‖a‖ := by ring


/-- The `𝓙` integrand (BBP (104)) as a function of `z`. -/
noncomputable def hJ {r : ℕ} (γ q v : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) *
    (((pc γ : ℂ) - z) ^ k * gFn k π z)

/-- Pointwise rescaling, `𝓙` side: with `a = σ(z - p_c)`, `q = p_c - ε/σ`,
`Z_M⁻¹ · (𝓙-integrand at z) = e^{εv} · e^{va} e^{-M(f(z)-f(p_c))} (g(z)/g(p_c)) a^k`. -/
theorem rescale_ptJ {r : ℕ} (γ q ε v σ : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) (hσ : 0 < σ)
    (hσdef : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ) (hq : q = pc γ - ε / σ)
    (hg : gFn k π (pc γ) ≠ 0) :
    (ZM γ q M k π)⁻¹ * hJ γ q v M k π z =
      ((Real.exp (ε * v) : ℝ) : ℂ) *
        (exp ((v : ℂ) * ((σ : ℂ) * (z - pc γ))) *
          (exp (-(M : ℂ) * (fFn γ q z - fFn γ q (pc γ))) * (gFn k π z / gFn k π (pc γ))) *
          ((σ : ℂ) * (z - pc γ)) ^ k) := by
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have e1 : exp (((σ * v : ℝ) : ℂ) * (z - q)) =
      ((Real.exp (ε * v) : ℝ) : ℂ) * exp ((v : ℂ) * ((σ : ℂ) * (z - pc γ))) := by
    rw [ofReal_exp, ← Complex.exp_add]; congr 1; rw [hq]; push_cast; field_simp; ring
  have e2 : exp (-(M : ℂ) * fFn γ q z) =
      exp (-(M : ℂ) * fFn γ q (pc γ)) * exp (-(M : ℂ) * (fFn γ q z - fFn γ q (pc γ))) := by
    rw [← Complex.exp_add]; ring_nf
  have e3 : ((σ : ℂ) * (z - pc γ)) ^ k = (-(σ : ℂ)) ^ k * ((pc γ : ℂ) - z) ^ k := by
    rw [← mul_pow]; ring
  have e4 : exp (-(M : ℂ) * fFn γ q (pc γ)) = (exp ((M : ℂ) * fFn γ q (pc γ)))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  unfold ZM hJ
  rw [hσdef, e1, e2, e3, e4]
  have hE : exp ((M : ℂ) * fFn γ q (pc γ)) ≠ 0 := Complex.exp_ne_zero _
  have hs : (-(σ : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hσ0)
  field_simp

set_option maxHeartbeats 1000000 in
/-- J connector core: on `a = x + R e^{iθ}` (`cos θ = -1/2`) with `c ≤ x ≤ 0`, `R ≥ -2c`, the
rescaled integrand `e^{va} e^F G a^k` is at most `B e^{cv} e^{-R}` (cubic decay in `R`). -/
theorem conn_coreJ (c θ V₀ K : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = -(1 / 2))
    (hsin : Real.sin θ ^ 2 = 3 / 4) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (v x R s : ℝ) (F G : ℂ), V₀ ≤ v → c ≤ x → x ≤ 0 → -2 * c ≤ R → 0 ≤ s →
      ‖F - -(((x : ℂ) + (R : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3)‖ ≤
        K * s * ‖(x : ℂ) + (R : ℂ) * exp ((θ : ℂ) * I)‖ ^ 4 →
      ‖G - 1‖ ≤ K * s * ‖(x : ℂ) + (R : ℂ) * exp ((θ : ℂ) * I)‖ →
      K * s * ‖(x : ℂ) + (R : ℂ) * exp ((θ : ℂ) * I)‖ ≤ 1 / 8 →
      ‖exp ((v : ℂ) * ((x : ℂ) + (R : ℂ) * exp ((θ : ℂ) * I))) * (exp F * G) *
          ((x : ℂ) + (R : ℂ) * exp ((θ : ℂ) * I)) ^ k‖ ≤
        B * Real.exp (c * v) * Real.exp (-R) := by
  obtain ⟨D, hD⟩ := cubic_bound (2 * (|V₀| / 2 + c ^ 2 / 2 + 3 * c ^ 2 / 8 + (k : ℝ) + 1))
    (4 * (-3 * c / 8))
  refine ⟨2 * Real.exp (D + |V₀| * (-c) - c ^ 3 / 3 - c ^ 3 / 8 - (k : ℝ) * c), by positivity,
    fun v x R s F G hv hcx hx0 hR hs hF hG hsm => ?_⟩
  set a : ℂ := (x : ℂ) + (R : ℂ) * exp ((θ : ℂ) * I) with ha
  have hR0 : 0 ≤ R := by linarith only [hcx, hx0, hR]
  have hre : a.re = x - R / 2 := by
    rw [ha, Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im, hcos]; ring
  have him : a.im = R * Real.sin θ := by
    rw [ha, Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]; ring
  have him2 : a.im ^ 2 = 3 / 4 * R ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hn0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hnhi : ‖a‖ ≤ R - c := by
    have h1 := norm_add_le (x : ℂ) ((R : ℂ) * exp ((θ : ℂ) * I))
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real, Real.norm_of_nonneg hR0,
      Real.norm_eq_abs, abs_of_nonpos hx0] at h1
    rw [ha]; linarith only [hcx, h1]
  have hE1 : ‖exp ((v : ℂ) * a)‖ = Real.exp (v * (x - R / 2)) := by
    rw [Complex.norm_exp, Complex.re_ofReal_mul, hre]
  have hE3 : ‖a ^ k‖ ≤ Real.exp ((k : ℝ) * (R - c)) := by
    rw [norm_pow, Real.exp_nat_mul]
    apply pow_le_pow_left₀ hn0
    have := Real.add_one_le_exp (R - c)
    linarith only [hnhi, this]
  have hreA : (-(a ^ 3 / 3)).re = -x ^ 3 / 3 + x ^ 2 * R / 2 + x * R ^ 2 / 2 - R ^ 3 / 3 := by
    have e : -(a ^ 3 / 3) = ((-1 / 3 : ℝ) : ℂ) * a ^ 3 := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, re_cube, him2, hre]; ring
  have hxle : ‖F - -(a ^ 3 / 3)‖ ≤ (R - c) ^ 3 / 8 := by
    have h3 : 0 ≤ ‖a‖ ^ 3 := pow_nonneg hn0 3
    have h4 : ‖a‖ ^ 3 ≤ (R - c) ^ 3 := pow_le_pow_left₀ hn0 hnhi 3
    calc ‖F - -(a ^ 3 / 3)‖ ≤ K * s * ‖a‖ ^ 4 := hF
      _ = (K * s * ‖a‖) * ‖a‖ ^ 3 := by ring
      _ ≤ 1 / 8 * ‖a‖ ^ 3 := mul_le_mul_of_nonneg_right hsm h3
      _ ≤ (R - c) ^ 3 / 8 := by linarith only [h4]
  have hFre : F.re ≤ (-(a ^ 3 / 3)).re + (R - c) ^ 3 / 8 := by
    have h1 : (F - -(a ^ 3 / 3)).re ≤ ‖F - -(a ^ 3 / 3)‖ := Complex.re_le_norm _
    rw [Complex.sub_re] at h1; linarith only [hxle, h1]
  have hGn : ‖G‖ ≤ 2 := by
    have h1 := norm_le_norm_add_norm_sub' G 1
    have h2 : 0 ≤ K * s * ‖a‖ := by positivity
    rw [norm_one] at h1; linarith only [hG, hsm, h1]
  have hvx : v * (x - R / 2) ≤ c * v + |V₀| * (R / 2) := by
    rcases le_total 0 v with h | h
    · have h1 : 0 ≤ v * (c - (x - R / 2)) := mul_nonneg h (by linarith only [hx0, hR])
      have h2 : 0 ≤ |V₀| * (R / 2) := mul_nonneg (abs_nonneg _) (by linarith only [hR0])
      linarith only [h1, h2]
    · have h2 : -|V₀| ≤ v := le_trans (neg_abs_le V₀) hv
      have hp : 0 ≤ R / 2 - x + c := by linarith only [hx0, hR]
      have h3 : (-v) * (R / 2 - x + c) ≤ |V₀| * (R / 2 - x + c) :=
        mul_le_mul_of_nonneg_right (by linarith only [h2]) hp
      have h4 : |V₀| * (R / 2 - x + c) ≤ |V₀| * (R / 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [hcx]) (abs_nonneg _)
      linarith only [h3, h4]
  have hx3 : -x ^ 3 ≤ -c ^ 3 := by
    have h1 : 0 ≤ (x - c) * ((x + c / 2) ^ 2 + 3 * c ^ 2 / 4) :=
      mul_nonneg (by linarith only [hcx]) (by positivity)
    linarith only [h1]
  have hx2 : x ^ 2 ≤ c ^ 2 := by nlinarith
  have hx2R : x ^ 2 * R ≤ c ^ 2 * R := mul_le_mul_of_nonneg_right hx2 hR0
  have hxR2 : 0 ≤ (-x) * R ^ 2 := mul_nonneg (by linarith only [hx0]) (sq_nonneg R)
  have hD' := hD (R / 2) (by linarith only [hR0])
  have hR3 : 0 ≤ R ^ 3 := pow_nonneg hR0 3
  have hexp : v * (x - R / 2) + ((-(a ^ 3 / 3)).re + (R - c) ^ 3 / 8) + (k : ℝ) * (R - c) ≤
      (D + |V₀| * (-c) - c ^ 3 / 3 - c ^ 3 / 8 - (k : ℝ) * c) + c * v + -R := by
    rw [hreA]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have habs : 0 ≤ |V₀| * (-c) := mul_nonneg (abs_nonneg _) (by linarith only [hcx, hx0])
    linarith only [hvx, hx3, hx2R, hxR2, hD', hR3, habs]
  rw [norm_mul, norm_mul, norm_mul, hE1, Complex.norm_exp]
  calc Real.exp (v * (x - R / 2)) * (Real.exp F.re * ‖G‖) * ‖a ^ k‖
      ≤ Real.exp (v * (x - R / 2)) * (Real.exp ((-(a ^ 3 / 3)).re + (R - c) ^ 3 / 8) * 2) *
          Real.exp ((k : ℝ) * (R - c)) := by
        gcongr
    _ = 2 * Real.exp (v * (x - R / 2) + ((-(a ^ 3 / 3)).re + (R - c) ^ 3 / 8) +
          (k : ℝ) * (R - c)) := by
        simp only [Real.exp_add]; ring
    _ ≤ 2 * Real.exp ((D + |V₀| * (-c) - c ^ 3 / 3 - c ^ 3 / 8 - (k : ℝ) * c) + c * v + -R) := by
        gcongr
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

set_option maxHeartbeats 2000000 in
/-- J-connector: the short horizontal piece `w₀ + δe^{iθ} + s`, `s ∈ [0, 2ε/σ]`, `w₀ = p_c - 2ε/σ`,
of `Σ*` contributes `O(e^{-εv}/m)` to `𝓙/Z_M`. -/
theorem conn_pieceJ (ε V₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ) (hε : 0 < ε) (hcos : Real.cos θ = -(1 / 2))
    (hsin : Real.sin θ ^ 2 = 3 / 4) (hC₁ : 0 ≤ C₁) (hK₂ : 0 ≤ K₂) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + 2 * ε / σ ≤ δ₀ →
      (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 → 4 * ε ≤ σ * δ →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      gFn k π (pc γ) ≠ 0 →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ s in (0 : ℝ)..(pc γ - (pc γ + (-2 * ε) / σ)), hJ γ q v M k π
            (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) + (δ : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ))‖ ≤
        B * Real.exp (-ε * v) / m := by
  have hc : -2 * ε < 0 := by linarith only [hε]
  obtain ⟨B1, hB1, hcore⟩ := conn_coreJ (-2 * ε) θ V₀ (C₁ + 2 * K₂) k hc hcos hsin (by linarith only [hC₁, hK₂])
  refine ⟨B1 * (2 * ε) / (2 * Real.pi) / δ, by positivity, ?_⟩
  intro r π γ q v m σ M hv hm1 hm3 hν hσdef hσ hq hδ0 hsm h4 hTay hGr hg0
  have hm0 : 0 < m := by linarith only [hm1]
  have hν0 : 0 < nu γ := by linarith only [hν]
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have hL : pc γ - (pc γ + (-2 * ε) / σ) = 2 * ε / σ := by field_simp; ring
  have hL0 : 0 ≤ 2 * ε / σ := by positivity
  have he0 : 0 ≤ Real.exp (ε * v) := (Real.exp_pos _).le
  have hpt : ∀ s ∈ Set.uIoc (0 : ℝ) (pc γ - (pc γ + (-2 * ε) / σ)),
      ‖(ZM γ q M k π)⁻¹ * hJ γ q v M k π (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
          (δ : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ))‖ ≤
        Real.exp (ε * v) * (B1 * Real.exp (-2 * ε * v) * Real.exp (-(σ * δ))) := by
    intro s hs
    rw [hL, Set.uIoc_of_le hL0] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have hx0 : -2 * ε + σ * s ≤ 0 := by
      have : σ * s ≤ σ * (2 * ε / σ) := mul_le_mul_of_nonneg_left hs1 hσ0.le
      have h2 : σ * (2 * ε / σ) = 2 * ε := by field_simp
      linarith only [this, h2]
    have hcx : -2 * ε ≤ -2 * ε + σ * s := by nlinarith
    have hzf : (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) + (δ : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ)) =
        (pc γ : ℂ) + (((-2 * ε + σ * s : ℝ) : ℂ) + ((σ * δ : ℝ) : ℂ) * exp ((θ : ℂ) * I)) /
          (σ : ℂ) := by push_cast; field_simp; ring
    rw [hzf]
    set a : ℂ := ((-2 * ε + σ * s : ℝ) : ℂ) + ((σ * δ : ℝ) : ℂ) * exp ((θ : ℂ) * I) with ha
    have hnA : ‖a‖ ≤ σ * δ + 2 * ε := by
      have h1 := norm_add_le ((-2 * ε + σ * s : ℝ) : ℂ) (((σ * δ : ℝ) : ℂ) * exp ((θ : ℂ) * I))
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ σ * δ), Real.norm_eq_abs,
        abs_of_nonpos hx0] at h1
      rw [ha]; linarith only [hcx, h1]
    have hd : ‖(pc γ : ℂ) + a / (σ : ℂ) - pc γ‖ ≤ δ₀ := by
      rw [add_sub_cancel_left, norm_div, norm_real, Real.norm_of_nonneg hσ0.le, div_le_iff₀ hσ0]
      have h3 : (δ + 2 * ε / σ) * σ ≤ δ₀ * σ := mul_le_mul_of_nonneg_right hδ0 hσ0.le
      have h4' : (δ + 2 * ε / σ) * σ = σ * δ + 2 * ε := by field_simp
      linarith only [hnA, h3, h4']
    obtain ⟨hg0z, hGb⟩ := hGr _ hd
    have hTb := hTay _ hd
    have hres := rescale_ptJ γ q ε v σ M k π ((pc γ : ℂ) + a / (σ : ℂ)) hσ0 hσdef hq hg0
    have hsa : (σ : ℂ) * ((pc γ : ℂ) + a / (σ : ℂ) - pc γ) = a := by field_simp; ring
    rw [hsa] at hres
    have hF := F_scale γ q m σ C₁ M _ hm0 hm3 hν hσ hC₁ hTb
    have hG := G_scale γ K₂ m σ _ _ hm0 hν hσ hK₂ hGb
    have hn0 := norm_nonneg a
    have hs0' : 0 ≤ 1 / m := by positivity
    have h5 : (1 / m) * ‖a‖ ≤ nu γ * δ + 2 * ε / m := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm0]
      have h7 : σ * δ = nu γ * δ * m := by rw [hσ]; ring
      have h9 : (nu γ * δ + 2 * ε / m) * m = nu γ * δ * m + 2 * ε := by field_simp
      linarith only [hnA, h7, h9]
    have hCK : 0 ≤ C₁ + 2 * K₂ := by linarith only [hC₁, hK₂]
    have hX0 : 0 ≤ (1 / m) * ‖a‖ := by positivity
    have hsm' : (C₁ + 2 * K₂) * (1 / m) * ‖a‖ ≤ 1 / 8 := by
      calc (C₁ + 2 * K₂) * (1 / m) * ‖a‖ = (C₁ + 2 * K₂) * ((1 / m) * ‖a‖) := by ring
        _ ≤ (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) := mul_le_mul_of_nonneg_left h5 hCK
        _ ≤ 1 / 8 := hsm
    have hF' : ‖-(M : ℂ) * (fFn γ q ((pc γ : ℂ) + a / (σ : ℂ)) - fFn γ q (pc γ)) -
        -(a ^ 3 / 3)‖ ≤ (C₁ + 2 * K₂) * (1 / m) * ‖a‖ ^ 4 := by
      rw [show ∀ X Y : ℂ, -(M : ℂ) * X - -Y = -((M : ℂ) * X - Y) from fun X Y => by ring,
        norm_neg]
      refine hF.trans ?_
      have : 0 ≤ (1 / m) * ‖a‖ ^ 4 := by positivity
      nlinarith
    have hη : K₂ * (1 / m) * ‖a‖ ≤ 1 / 2 := by
      have : K₂ * (1 / m) * ‖a‖ ≤ (C₁ + 2 * K₂) * (1 / m) * ‖a‖ := by
        have e1 : K₂ * (1 / m) * ‖a‖ = K₂ * ((1 / m) * ‖a‖) := by ring
        have e2 : (C₁ + 2 * K₂) * (1 / m) * ‖a‖ = (C₁ + 2 * K₂) * ((1 / m) * ‖a‖) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right (by linarith only [hC₁, hK₂]) hX0
      linarith only [hsm', this]
    obtain ⟨-, hGinv⟩ := inv_ratio _ _ hG hη
    rw [inv_div] at hGinv
    have hG' : ‖gFn k π ((pc γ : ℂ) + a / (σ : ℂ)) / gFn k π (pc γ) - 1‖ ≤
        (C₁ + 2 * K₂) * (1 / m) * ‖a‖ := by
      refine hGinv.trans ?_
      have e1 : 2 * (K₂ * (1 / m) * ‖a‖) = (2 * K₂) * ((1 / m) * ‖a‖) := by ring
      have e2 : (C₁ + 2 * K₂) * (1 / m) * ‖a‖ = (C₁ + 2 * K₂) * ((1 / m) * ‖a‖) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (by linarith only [hC₁]) hX0
    have hR : -2 * (-2 * ε) ≤ σ * δ := by linarith only [h4]
    have hb := hcore v (-2 * ε + σ * s) (σ * δ) (1 / m) _ _ hv hcx hx0 hR hs0' hF' hG' hsm'
    rw [hres, norm_mul, norm_real, Real.norm_of_nonneg he0]
    exact mul_le_mul_of_nonneg_left hb he0
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [hL, sub_zero, abs_of_nonneg hL0] at hI
  rw [hL]
  rw [mul_comm (ZM γ q M k π)⁻¹ _, mul_assoc, ← intervalIntegral.integral_const_mul, norm_mul,
    norm_real, Real.norm_of_nonneg (by positivity)]
  have hexpT : Real.exp (-(σ * δ)) ≤ 1 / (m * δ) := by
    have h1 : m * δ ≤ σ * δ := by
      have h0 : 1 * (m * δ) ≤ nu γ * (m * δ) := mul_le_mul_of_nonneg_right hν (by positivity)
      rw [hσ]; linarith only [h0]
    have h2 : σ * δ + 1 ≤ Real.exp (σ * δ) := Real.add_one_le_exp _
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith only [h1, h2]
  have hEE : Real.exp (ε * v) * Real.exp (-2 * ε * v) = Real.exp (-ε * v) := by
    rw [← Real.exp_add]; ring_nf
  have hc0 : 0 ≤ Real.exp (-2 * ε * v) := (Real.exp_pos _).le
  have hσπ : 0 ≤ σ / (2 * Real.pi) := by positivity
  calc σ / (2 * Real.pi) * ‖∫ s in (0 : ℝ)..(2 * ε / σ), (ZM γ q M k π)⁻¹ * hJ γ q v M k π
        (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) + (δ : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ))‖
      ≤ σ / (2 * Real.pi) * (Real.exp (ε * v) * (B1 * Real.exp (-2 * ε * v) *
          Real.exp (-(σ * δ))) * (2 * ε / σ)) := mul_le_mul_of_nonneg_left hI hσπ
    _ = B1 * (2 * ε) / (2 * Real.pi) * (Real.exp (ε * v) * Real.exp (-2 * ε * v)) *
          Real.exp (-(σ * δ)) := by field_simp
    _ ≤ B1 * (2 * ε) / (2 * Real.pi) * (Real.exp (ε * v) * Real.exp (-2 * ε * v)) *
          (1 / (m * δ)) := by
        apply mul_le_mul_of_nonneg_left hexpT; positivity
    _ = _ := by rw [hEE]; field_simp

end P31J2

open Complex MeasureTheory SpikedWishart.SoftEdge in
theorem solution :
    ∀ (ε V₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = -(1 / 2) →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + 2 * ε / σ ≤ δ₀ →
      (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 → 4 * ε ≤ σ * δ →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      gFn k π (pc γ) ≠ 0 →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ s in (0 : ℝ)..(pc γ - (pc γ + (-2 * ε) / σ)), (fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) * (((pc γ : ℂ) - z) ^ k * gFn k π z))
            (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) + (δ : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ))‖ ≤
        B * Real.exp (-ε * v) / m := by
  exact P31J2.conn_pieceJ
