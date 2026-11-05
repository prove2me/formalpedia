-- Prove2me | solution 1 for SpikedWishart.SoftEdge.H_near_ray
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T08:15:13.516016+00:00
-- url     : https://prove2.me/submissions/5376e25d-f67f-4fcc-a9f8-acc369b96395

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option linter.all false
set_option Elab.async false
open Complex

namespace P31E
open SpikedWishart.SoftEdge MeasureTheory


/-- `‖e^x - 1‖ ≤ 2‖x‖ e^{‖x‖}` for every complex `x`. -/
theorem norm_exp_sub_one_le' (x : ℂ) : ‖exp x - 1‖ ≤ 2 * ‖x‖ * Real.exp ‖x‖ := by
  have h1 : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg x)
  rcases le_total ‖x‖ 1 with hx | hx
  · have := Complex.norm_exp_sub_one_le hx
    have h2 : 0 ≤ 2 * ‖x‖ := by positivity
    exact this.trans (le_mul_of_one_le_right h2 h1)
  · have h3 : ‖exp x‖ ≤ Real.exp ‖x‖ := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (Complex.re_le_norm x)
    calc ‖exp x - 1‖ ≤ ‖exp x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp ‖x‖ + 1 := by rw [norm_one]; linarith
      _ ≤ 2 * ‖x‖ * Real.exp ‖x‖ := by
          have h4 := mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 2 * ‖x‖ by linarith) (Real.exp_pos ‖x‖).le
          linarith

theorem cubic_bound (A B : ℝ) : ∃ D : ℝ, ∀ t : ℝ, 0 ≤ t → A * t + B * t ^ 2 - t ^ 3 / 3 ≤ D := by
  have hL0 : 0 ≤ |A| + |B| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨(|A| + |B|) + 9 * (|A| + |B|) ^ 3, fun t ht => ?_⟩
  have hA : A * t ≤ |A| * t := mul_le_mul_of_nonneg_right (le_abs_self A) ht
  have hB : B * t ^ 2 ≤ |B| * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg t)
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
  have hL3 : 0 ≤ (|A| + |B|) ^ 3 := pow_nonneg hL0 3
  rcases le_total t 1 with h1 | h1
  · have h1A : |A| * t ≤ |A| := mul_le_of_le_one_right (abs_nonneg A) h1
    have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht h1
    have h1B : |B| * t ^ 2 ≤ |B| := mul_le_of_le_one_right (abs_nonneg B) ht2
    linarith
  · have hAt : |A| * t ≤ |A| * t ^ 2 := by
      have : t ≤ t ^ 2 := le_self_pow₀ h1 (by norm_num)
      exact mul_le_mul_of_nonneg_left this (abs_nonneg A)
    rcases le_total t (3 * (|A| + |B|)) with h2 | h2
    · have h9 : t ^ 2 ≤ 9 * (|A| + |B|) ^ 2 := by have := pow_le_pow_left₀ ht h2 2; linarith
      have h9' := mul_le_mul_of_nonneg_left h9 hL0
      linarith
    · have hneg := mul_nonneg (sq_nonneg t) (sub_nonneg.2 h2)
      linarith


set_option maxHeartbeats 1000000 in
/-- E-near core (BBP (148)-(152)): on the ray `a = c + τ e^{iθ}` (`cos θ = 1/2`), if `F` is within
`K s ‖a‖⁴` of `a³/3` and `G` within `K s ‖a‖` of `1`, and `K s ‖a‖ ≤ 1/8`, then the integrand of
`e^{-ua}(e^F G - e^{a³/3}) a^{-k}` is at most `B s e^{-cu} e^{-τ}`, uniformly for `u ≥ U₀`. -/
theorem near_core (c θ U₀ K : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (u τ s : ℝ) (F G : ℂ), U₀ ≤ u → 0 ≤ τ → 0 ≤ s →
      ‖F - ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3‖ ≤
        K * s * ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 4 →
      ‖G - 1‖ ≤ K * s * ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ →
      K * s * ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤ 1 / 8 →
      ‖exp (-(u : ℂ) * ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))) *
          (exp F * G - exp (((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3)) *
          (1 / ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ k)‖ ≤
        B * s * Real.exp (-c * u) * Real.exp (-τ) := by
  obtain ⟨D, hD⟩ := cubic_bound (2 * (-U₀ / 2 + c ^ 2 / 2 + 3 * c ^ 2 / 8 + 5))
    (4 * (-c / 2 - 3 * c / 8))
  have h2c : 0 ≤ 2 / -c := div_nonneg (by norm_num) (by linarith)
  refine ⟨5 * K * (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3 - c ^ 3 / 8 - 4 * c), by positivity,
    fun u τ s F G hu hτ hs hF hG hsm => ?_⟩
  set a : ℂ := (c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I) with ha
  set n : ℝ := ‖a‖ with hn
  have hre : a.re = c + τ / 2 := by
    rw [ha, Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im, hcos]; ring
  have him : a.im = τ * Real.sin θ := by
    rw [ha, Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]; ring
  have him2 : a.im ^ 2 = 3 / 4 * τ ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hn2 : n ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [hn, Complex.sq_norm, Complex.normSq_apply]; ring
  have hn0 : 0 ≤ n := norm_nonneg a
  have hnlo : -c / 2 ≤ n := by
    have h : (-c / 2) ^ 2 ≤ n ^ 2 := by rw [hn2, hre, him2]; linarith [sq_nonneg (c / 2 + τ), sq_nonneg c]
    exact (pow_le_pow_iff_left₀ (by linarith) hn0 two_ne_zero).1 h
  have hnhi : n ≤ τ - c := by
    have h1 := norm_add_le (c : ℂ) ((τ : ℂ) * exp ((θ : ℂ) * I))
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real, Real.norm_of_nonneg hτ,
      Real.norm_eq_abs, abs_of_neg hc] at h1
    rw [hn, ha]; linarith
  have hnpos : 0 < n := by linarith
  -- the factor e^{-ua}
  have hE1 : ‖exp (-(u : ℂ) * a)‖ = Real.exp (-u * (c + τ / 2)) := by
    rw [Complex.norm_exp]; congr 1
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, ofReal_re, ofReal_im, hre]; ring
  -- the factor a^{-k}
  have hE3 : ‖1 / a ^ k‖ ≤ (2 / -c) ^ k := by
    rw [norm_div, norm_one, norm_pow, ← hn, one_div, ← inv_pow]
    apply pow_le_pow_left₀ (inv_nonneg.mpr hn0)
    rw [inv_le_comm₀ hnpos (div_pos two_pos (by linarith))]
    rw [inv_div]; linarith
  -- Re(a³/3)
  have hreA : (a ^ 3 / 3).re = c ^ 3 / 3 + c ^ 2 / 2 * τ - c / 2 * τ ^ 2 - τ ^ 3 / 3 := by
    have : (a ^ 3 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) * a ^ 3 := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
    have hc3 : (a ^ 3).re = a.re ^ 3 - 3 * a.re * a.im ^ 2 := by
      rw [show a ^ 3 = a * a * a by ring, Complex.mul_re, Complex.mul_re, Complex.mul_im]; ring
    rw [hc3, him2, hre]; ring
  -- the middle factor
  set x : ℂ := F - a ^ 3 / 3 with hx
  have hKsn : 0 ≤ K * s * n := by positivity
  have hxle : ‖x‖ ≤ n ^ 3 / 8 := by
    have : K * s * n ^ 4 = (K * s * n) * n ^ 3 := by ring
    have h3 : 0 ≤ n ^ 3 := pow_nonneg hn0 3
    calc ‖x‖ ≤ K * s * n ^ 4 := hF
      _ = (K * s * n) * n ^ 3 := this
      _ ≤ 1 / 8 * n ^ 3 := mul_le_mul_of_nonneg_right hsm h3
      _ = n ^ 3 / 8 := by ring
  have hGn : ‖G‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' G 1
    rw [norm_one] at this; linarith
  have hsplit : exp F * G - exp (a ^ 3 / 3) =
      exp (a ^ 3 / 3) * ((exp x - 1) * G + (G - 1)) := by
    have : F = a ^ 3 / 3 + x := by rw [hx]; ring
    rw [this, Complex.exp_add]; ring
  have hexA : ‖exp (a ^ 3 / 3)‖ = Real.exp (c ^ 3 / 3 + c ^ 2 / 2 * τ - c / 2 * τ ^ 2 - τ ^ 3 / 3) := by
    rw [Complex.norm_exp, hreA]
  have hex1 := norm_exp_sub_one_le' x
  have hexx : Real.exp ‖x‖ ≤ Real.exp (n ^ 3 / 8) := Real.exp_le_exp.mpr hxle
  have hen : 1 ≤ Real.exp (n ^ 3 / 8) := Real.one_le_exp (by positivity)
  have hmid : ‖(exp x - 1) * G + (G - 1)‖ ≤ K * s * (4 * n ^ 4 + n) * Real.exp (n ^ 3 / 8) := by
    have hxK : ‖x‖ ≤ K * s * n ^ 4 := hF
    calc ‖(exp x - 1) * G + (G - 1)‖ ≤ ‖exp x - 1‖ * ‖G‖ + ‖G - 1‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (2 * ‖x‖ * Real.exp ‖x‖) * 2 + K * s * n :=
          add_le_add (mul_le_mul hex1 hGn (norm_nonneg _) (by positivity)) hG
      _ ≤ (2 * (K * s * n ^ 4) * Real.exp (n ^ 3 / 8)) * 2 + K * s * n * Real.exp (n ^ 3 / 8) := by
          have h1 : 2 * ‖x‖ * Real.exp ‖x‖ ≤ 2 * (K * s * n ^ 4) * Real.exp (n ^ 3 / 8) :=
            mul_le_mul (by linarith) hexx (by positivity) (by positivity)
          have h2 : K * s * n ≤ K * s * n * Real.exp (n ^ 3 / 8) := le_mul_of_one_le_right hKsn hen
          linarith
      _ = K * s * (4 * n ^ 4 + n) * Real.exp (n ^ 3 / 8) := by ring
  -- polynomial factor into an exponential
  have hpoly : 4 * n ^ 4 + n ≤ 5 * Real.exp (4 * (τ - c)) := by
    have h1 : 1 + n ≤ Real.exp n := by linarith [Real.add_one_le_exp n]
    have h2 : (1 + n) ^ 4 ≤ Real.exp n ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
    rw [← Real.exp_nat_mul] at h2
    have h3 : Real.exp ((4 : ℕ) * n) ≤ Real.exp (4 * (τ - c)) := by
      rw [Real.exp_le_exp]; push_cast; linarith
    have h4 : 4 * n ^ 4 + n ≤ 5 * (1 + n) ^ 4 := by linarith [pow_nonneg hn0 2, pow_nonneg hn0 3, pow_nonneg hn0 4]
    linarith
  have hn3 : n ^ 3 ≤ (τ - c) ^ 3 := pow_le_pow_left₀ hn0 hnhi 3
  -- assemble
  have hD' := hD (τ / 2) (by linarith)
  have hexp_total : Real.exp (-u * (c + τ / 2)) *
      (Real.exp (c ^ 3 / 3 + c ^ 2 / 2 * τ - c / 2 * τ ^ 2 - τ ^ 3 / 3) *
        (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c)))) ≤
      Real.exp (D + c ^ 3 / 3 - c ^ 3 / 8 - 4 * c) * Real.exp (-c * u) * Real.exp (-τ) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      Real.exp_le_exp]
    have hu' : -u * (τ / 2) ≤ -U₀ * (τ / 2) := by have := mul_le_mul_of_nonneg_right hu (show (0:ℝ) ≤ τ / 2 by linarith); linarith
    have ht3 : 0 ≤ τ ^ 3 := pow_nonneg hτ 3
    linarith [hu', hn3, hD', ht3]
  rw [norm_mul, norm_mul, hE1, hsplit, norm_mul, hexA]
  have hm0 : 0 ≤ ‖(exp x - 1) * G + (G - 1)‖ := norm_nonneg _
  have hmid' : ‖(exp x - 1) * G + (G - 1)‖ ≤
      5 * K * s * (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c))) := by
    calc ‖(exp x - 1) * G + (G - 1)‖ ≤ K * s * (4 * n ^ 4 + n) * Real.exp (n ^ 3 / 8) := hmid
      _ ≤ K * s * (5 * Real.exp (4 * (τ - c))) * Real.exp (n ^ 3 / 8) := by
          gcongr
      _ = 5 * K * s * (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c))) := by ring
  have hP0 : 0 ≤ Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c)) := by positivity
  calc Real.exp (-u * (c + τ / 2)) *
        (Real.exp (c ^ 3 / 3 + c ^ 2 / 2 * τ - c / 2 * τ ^ 2 - τ ^ 3 / 3) *
          ‖(exp x - 1) * G + (G - 1)‖) * ‖1 / a ^ k‖
      ≤ Real.exp (-u * (c + τ / 2)) *
        (Real.exp (c ^ 3 / 3 + c ^ 2 / 2 * τ - c / 2 * τ ^ 2 - τ ^ 3 / 3) *
          (5 * K * s * (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c))))) * (2 / -c) ^ k := by
        gcongr
    _ = 5 * K * s * (2 / -c) ^ k * (Real.exp (-u * (c + τ / 2)) *
        (Real.exp (c ^ 3 / 3 + c ^ 2 / 2 * τ - c / 2 * τ ^ 2 - τ ^ 3 / 3) *
          (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c))))) := by ring
    _ ≤ 5 * K * s * (2 / -c) ^ k * (Real.exp (D + c ^ 3 / 3 - c ^ 3 / 8 - 4 * c) *
          Real.exp (-c * u) * Real.exp (-τ)) := by
        gcongr
    _ = 5 * K * (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3 - c ^ 3 / 8 - 4 * c) * s *
          Real.exp (-c * u) * Real.exp (-τ) := by ring

/-- Integrating a pointwise `B e^{-τ}` bound over `[0, T]`. -/
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
  rw [h2] at h1; linarith [mul_nonneg hB h3.le]



/-- Pointwise rescaling (BBP (148)): with `a = σ(z - p_c)` and `q = p_c - ε/σ`,
`Z_M · (𝓗-integrand at z) = e^{-εu} · e^{-ua} e^{M(f(z)-f(p_c))} (g(p_c)/g(z)) a^{-k}`. -/
theorem rescale_pt {r : ℕ} (γ q ε u σ : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) (hσ : 0 < σ)
    (hσdef : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ) (hq : q = pc γ - ε / σ)
    (hz : (pc γ : ℂ) - z ≠ 0) (hg : gFn k π z ≠ 0) :
    ZM γ q M k π * (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)) *
        exp ((M : ℂ) * fFn γ q z) * (1 / (((pc γ : ℂ) - z) ^ k * gFn k π z))) =
      ((Real.exp (-ε * u) : ℝ) : ℂ) *
        (exp (-(u : ℂ) * ((σ : ℂ) * (z - pc γ))) *
          (exp ((M : ℂ) * (fFn γ q z - fFn γ q (pc γ))) * (gFn k π (pc γ) / gFn k π z)) *
          (1 / ((σ : ℂ) * (z - pc γ)) ^ k)) := by
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have e1 : exp (-((σ * u : ℝ) : ℂ) * (z - q)) =
      ((Real.exp (-ε * u) : ℝ) : ℂ) * exp (-(u : ℂ) * ((σ : ℂ) * (z - pc γ))) := by
    rw [ofReal_exp, ← Complex.exp_add]; congr 1; rw [hq]; push_cast; field_simp; ring
  have e2 : exp ((M : ℂ) * fFn γ q z) =
      exp ((M : ℂ) * fFn γ q (pc γ)) * exp ((M : ℂ) * (fFn γ q z - fFn γ q (pc γ))) := by
    rw [← Complex.exp_add]; ring_nf
  have e3 : ((σ : ℂ) * (z - pc γ)) ^ k = (-(σ : ℂ)) ^ k * ((pc γ : ℂ) - z) ^ k := by
    rw [← mul_pow]; ring
  unfold ZM
  rw [hσdef, e1, e2, e3]
  have hE : exp ((M : ℂ) * fFn γ q (pc γ)) ≠ 0 := Complex.exp_ne_zero _
  have hs : (-(σ : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hσ0)
  have hp : ((pc γ : ℂ) - z) ^ k ≠ 0 := pow_ne_zero _ hz
  field_simp

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


theorem re_cube (a : ℂ) : (a ^ 3).re = a.re ^ 3 - 3 * a.re * a.im ^ 2 := by
  rw [show a ^ 3 = a * a * a by ring, Complex.mul_re, Complex.mul_re, Complex.mul_im]
  ring

theorem ray_point_re_im (c t θ : ℝ) :
    ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)).re = c + t * Real.cos θ ∧
      ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)).im = t * Real.sin θ := by
  constructor
  · rw [Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im]
    ring
  · rw [Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]
    ring

/-- Pointwise bound for the `𝓗_∞` integrand on a ray `c + t e^{iθ}` with `cos θ = 1/2`. -/
theorem H_integrand_bound (c x0 θ D : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + 1) * t + (-c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (u : ℝ) (hu : x0 ≤ u) (t : ℝ) (ht : 0 < t) :
    ‖exp (-(u : ℂ) * ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) +
        ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) *
        (1 / ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ k)‖ ≤
      ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u)) * Real.exp (-t) := by
  set a : ℂ := (c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hre, him⟩ := ray_point_re_im c t θ
  rw [← ha] at hre him
  rw [hcos] at hre
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hwre : (-(u : ℂ) * a + a ^ 3 / 3).re = -u * a.re + (a.re ^ 3 - 3 * a.re * a.im ^ 2) / 3 := by
    rw [Complex.add_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, ofReal_re, ofReal_im]
    ring
  have hexp : (-(u : ℂ) * a + a ^ 3 / 3).re ≤ D + c ^ 3 / 3 + -c * u + -t := by
    rw [hwre, him2, hre]
    have h1 := hD t ht.le
    have h2 := mul_nonneg (sub_nonneg.2 hu) ht.le
    linarith
  have hnorm2 : (-c / 2) ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre]
    linarith [sq_nonneg (t + c / 2), him2, sq_nonneg c]
  have hc2 : 0 < -c / 2 := by linarith
  have hnorm : -c / 2 ≤ ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (norm_nonneg a) hlt
    linarith
  have hinv : 1 / ‖a‖ ≤ 2 / -c := by
    have := one_div_le_one_div_of_le hc2 hnorm
    calc 1 / ‖a‖ ≤ 1 / (-c / 2) := this
      _ = 2 / -c := by field_simp
  have hk : ‖1 / a ^ k‖ ≤ (2 / -c) ^ k := by
    rw [norm_div, norm_one, norm_pow, ← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) hinv k
  rw [norm_mul, norm_exp]
  calc Real.exp (-(u : ℂ) * a + a ^ 3 / 3).re * ‖1 / a ^ k‖
      ≤ Real.exp (D + c ^ 3 / 3 + -c * u + -t) * (2 / -c) ^ k :=
        mul_le_mul (Real.exp_le_exp.2 hexp) hk (norm_nonneg _) (Real.exp_pos _).le
    _ = ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u)) * Real.exp (-t) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring

-- NEW
/-- The `𝓗` integrand (BBP (103)) as a function of `z`. -/
noncomputable def hH {r : ℕ} (γ q u : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) *
    (1 / (((pc γ : ℂ) - z) ^ k * gFn k π z))

/-- The `𝓗_∞` integrand (BBP (120)). -/
noncomputable def phiH (u : ℝ) (k : ℕ) (a : ℂ) : ℂ := exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k)

theorem ray_norm_ge (c θ τ : ℝ) (hc : c < 0) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4) (hτ : 0 ≤ τ) :
    -c / 2 ≤ ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ := by
  have hre : ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)).re = c + τ / 2 := by
    rw [Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im, hcos]; ring
  have him : ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)).im = τ * Real.sin θ := by
    rw [Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]; ring
  have hn2 : ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 2 =
      (c + τ / 2) ^ 2 + 3 / 4 * τ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him, ← hsin]; ring
  have h : (-c / 2) ^ 2 ≤ ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 2 := by
    rw [hn2]; linarith [sq_nonneg (c / 2 + τ), sq_nonneg c]
  exact (pow_le_pow_iff_left₀ (by linarith) (norm_nonneg _) two_ne_zero).1 h

theorem ray_norm_le (c θ τ : ℝ) (hc : c < 0) (hτ : 0 ≤ τ) :
    ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤ τ - c := by
  have h1 := norm_add_le (c : ℂ) ((τ : ℂ) * exp ((θ : ℂ) * I))
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real, Real.norm_of_nonneg hτ,
    Real.norm_eq_abs, abs_of_neg hc] at h1
  linarith

/-- Taylor input in the rescaled variable: `‖M(f(p_c + a/σ) - f(p_c)) - a³/3‖ ≤ C₁ ‖a‖⁴ / m`. -/
theorem F_scale (γ q m σ C₁ : ℝ) (M : ℕ) (a : ℂ) (hm : 0 < m) (hm3 : m ^ 3 = (M : ℝ))
    (hν : 1 ≤ nu γ) (hσ : σ = nu γ * m) (hC : 0 ≤ C₁)
    (hT : ‖fFn γ q ((pc γ : ℂ) + a / σ) - fFn γ q (pc γ) -
        ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((pc γ : ℂ) + a / σ - pc γ) ^ 3‖ ≤
        C₁ * ‖(pc γ : ℂ) + a / σ - pc γ‖ ^ 4) :
    ‖(M : ℂ) * (fFn γ q ((pc γ : ℂ) + a / σ) - fFn γ q (pc γ)) - a ^ 3 / 3‖ ≤
      C₁ * (1 / m) * ‖a‖ ^ 4 := by
  have hν0 : 0 < nu γ := by linarith
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
  have hσ0 : 0 < σ := by rw [hσ]; exact mul_pos (by linarith) hm
  rw [add_sub_cancel_left, norm_div, norm_real, Real.norm_of_nonneg hσ0.le] at hG
  refine hG.trans ?_
  have h1 : ‖a‖ / σ ≤ (1 / m) * ‖a‖ := by
    rw [hσ, div_le_iff₀ (by positivity)]
    have : (1 / m) * ‖a‖ * (nu γ * m) = nu γ * ‖a‖ := by field_simp
    rw [this]; exact le_mul_of_one_le_left (norm_nonneg a) hν
  calc K₂ * (‖a‖ / σ) ≤ K₂ * ((1 / m) * ‖a‖) := mul_le_mul_of_nonneg_left h1 hK
    _ = K₂ * (1 / m) * ‖a‖ := by ring

theorem phi_ray_contOn (u c θ : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4) :
    ContinuousOn (fun τ : ℝ => phiH u k ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
      exp ((θ : ℂ) * I)) (Set.Ici 0) := by
  have hne : ∀ τ ∈ Set.Ici (0 : ℝ), ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ k ≠ 0 := by
    intro τ hτ
    apply pow_ne_zero
    intro h0
    have := ray_norm_ge c θ τ hc hcos hsin hτ
    rw [h0, norm_zero] at this; linarith
  unfold phiH
  apply ContinuousOn.mul _ continuousOn_const
  apply ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
  exact ContinuousOn.div continuousOn_const (Continuous.continuousOn (by fun_prop)) hne

theorem phi_ray_integrableOn (u c θ D x0 : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + 1) * t + (-c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (hu : x0 ≤ u) (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun τ : ℝ => phiH u k ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
      exp ((θ : ℂ) * I)) (Set.Ioi T) := by
  have hg : Integrable (fun τ : ℝ => ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) *
      Real.exp (-c * u)) * Real.exp (-τ)) (volume.restrict (Set.Ioi T)) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi T) _
  refine Integrable.mono' hg ?_ ?_
  · exact ((phi_ray_contOn u c θ k hc hcos hsin).mono
      (fun x hx => le_of_lt (lt_of_le_of_lt hT hx))).aestronglyMeasurable measurableSet_Ioi
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    exact H_integrand_bound c x0 θ D k hc hcos hsin hD u hu t (lt_of_le_of_lt hT ht)

theorem phi_ray_tail (u c θ D x0 : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + 1) * t + (-c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (hu : x0 ≤ u) (T : ℝ) (hT : 0 ≤ T) :
    ‖∫ τ in Set.Ioi T, phiH u k ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤
      ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u)) * Real.exp (-T) := by
  have hg : Integrable (fun τ : ℝ => ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) *
      Real.exp (-c * u)) * Real.exp (-τ)) (volume.restrict (Set.Ioi T)) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi T) _
  calc _ ≤ ∫ τ in Set.Ioi T, ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) *
        Real.exp (-c * u)) * Real.exp (-τ) := by
        apply norm_integral_le_of_norm_le hg
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall (fun t ht => ?_)
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
        exact H_integrand_bound c x0 θ D k hc hcos hsin hD u hu t (lt_of_le_of_lt hT ht)
    _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi]

set_option maxHeartbeats 2000000 in
/-- E-near for one ray of `Γ*` (BBP (148)-(152)): the rescaled near ray of `Z_M 𝓗` versus the
corresponding full ray of `𝓗_∞` with vertex `-ε/2`; error `B e^{-εu/2}/m`, `m = M^{1/3}`. -/
theorem near_ray (ε U₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ) (hε : 0 < ε) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4) (hC₁ : 0 ≤ C₁) (hK₂ : 0 ≤ K₂) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q u m σ : ℝ) (M : ℕ),
      U₀ ≤ u → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + ε / (2 * σ) ≤ δ₀ →
      (C₁ + K₂) * (nu γ * δ + ε / (2 * m)) ≤ 1 / 8 →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      ContinuousOn (hH γ q u M k π) (Metric.closedBall (pc γ : ℂ) δ₀ \ {(pc γ : ℂ)}) →
      ‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (0 : ℝ)..δ, hH γ q u M k π (((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) -
        ((Real.exp (-ε * u) / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (0 : ℝ), phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
            exp ((θ : ℂ) * I)‖ ≤
        B * Real.exp (-(ε / 2) * u) / m := by
  have hc : -ε / 2 < 0 := by linarith
  obtain ⟨B1, hB1, hcore⟩ := near_core (-ε / 2) θ U₀ (C₁ + K₂) k hc hcos hsin (by linarith)
  obtain ⟨D, hD⟩ := cubic_bound (-U₀ / 2 + (-ε / 2) ^ 2 / 2 + 1) (-(-ε / 2) / 2)
  have h2c : 0 ≤ 2 / -(-ε / 2) := div_nonneg (by norm_num) (by linarith)
  have hB2 : 0 ≤ (2 / -(-ε / 2)) ^ k * Real.exp (D + (-ε / 2) ^ 3 / 3) := by positivity
  refine ⟨(B1 + (2 / -(-ε / 2)) ^ k * Real.exp (D + (-ε / 2) ^ 3 / 3) / δ) / (2 * Real.pi),
    by positivity, ?_⟩
  intro r π γ q u m σ M hu hm1 hm3 hν hσdef hσ hq hδ0 hsm hTay hGr hcont
  have hm0 : 0 < m := by linarith
  have hν0 : 0 < nu γ := by linarith
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have hT0 : 0 ≤ σ * δ := by positivity
  have hw1 : ‖exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  rw [ray_rescale (hH γ q u M k π) (pc γ) (-ε / 2) σ δ (exp ((θ : ℂ) * I)) hσ0]
  -- distance of the rescaled ray to p_c
  have hzd : ∀ τ : ℝ, 0 ≤ τ → τ ≤ σ * δ →
      ‖(pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ) - pc γ‖ ≤ δ₀ := by
    intro τ h0 h1
    rw [add_sub_cancel_left, norm_div, norm_real, Real.norm_of_nonneg hσ0.le, div_le_iff₀ hσ0]
    have h2 := ray_norm_le (-ε / 2) θ τ hc h0
    have h3 : (δ + ε / (2 * σ)) * σ ≤ δ₀ * σ := mul_le_mul_of_nonneg_right hδ0 hσ0.le
    have h4 : (δ + ε / (2 * σ)) * σ = σ * δ + ε / 2 := by field_simp
    linarith
  -- pointwise comparison
  have hpt : ∀ τ : ℝ, 0 ≤ τ → τ ≤ σ * δ →
      ‖ZM γ q M k π * hH γ q u M k π
          ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
        ((Real.exp (-ε * u) : ℝ) : ℂ) *
          phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))‖ ≤
      (Real.exp (-ε * u) * (B1 * (1 / m) * Real.exp (-(-ε / 2) * u))) * Real.exp (-τ) := by
    intro τ h0 h1
    have hd := hzd τ h0 h1
    obtain ⟨hg0, hGb⟩ := hGr _ hd
    have hTb := hTay _ hd
    have hne : ((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I) ≠ 0 := by
      intro h
      have := ray_norm_ge (-ε / 2) θ τ hc hcos hsin h0
      rw [h, norm_zero] at this; linarith
    have hpz : (pc γ : ℂ) - ((pc γ : ℂ) +
        (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) ≠ 0 := by
      rw [show (pc γ : ℂ) - ((pc γ : ℂ) +
          (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) =
          -((((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) by ring]
      exact neg_ne_zero.mpr (div_ne_zero hne hσc)
    have hres := rescale_pt γ q ε u σ M k π _ hσ0 hσdef hq hpz hg0
    have hsa : (σ : ℂ) * ((pc γ : ℂ) +
        (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ) - pc γ) =
        ((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I) := by
      field_simp; ring
    rw [hsa] at hres
    have hF := F_scale γ q m σ C₁ M _ hm0 hm3 hν hσ hC₁ hTb
    have hG := G_scale γ K₂ m σ _ _ hm0 hν hσ hK₂ hGb
    have hnA := ray_norm_le (-ε / 2) θ τ hc h0
    have hn0 := norm_nonneg (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))
    have hs0 : 0 ≤ 1 / m := by positivity
    have hF' : ‖(M : ℂ) * (fFn γ q ((pc γ : ℂ) +
        (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) - fFn γ q (pc γ)) -
        (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3‖ ≤
        (C₁ + K₂) * (1 / m) * ‖((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 4 := by
      refine hF.trans ?_
      have : 0 ≤ (1 / m) * ‖((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 4 := by positivity
      linarith [mul_le_mul_of_nonneg_right (show C₁ ≤ C₁ + K₂ by linarith) this]
    have hG' : ‖gFn k π (pc γ) / gFn k π ((pc γ : ℂ) +
        (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) - 1‖ ≤
        (C₁ + K₂) * (1 / m) * ‖((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ := by
      refine hG.trans ?_
      have : 0 ≤ (1 / m) * ‖((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ := by positivity
      linarith [mul_le_mul_of_nonneg_right (show K₂ ≤ C₁ + K₂ by linarith) this]
    have hsm' : (C₁ + K₂) * (1 / m) * ‖((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤
        1 / 8 := by
      have h5 : (1 / m) * ‖((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤
          nu γ * δ + ε / (2 * m) := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm0]
        have h6 : τ - -ε / 2 ≤ σ * δ + ε / 2 := by linarith
        have h7 : σ * δ = nu γ * δ * m := by rw [hσ]; ring
        have h8 : ε / 2 ≤ ε / 2 * m := le_mul_of_one_le_right (by linarith) hm1
        have h9 : ε / (2 * m) * m = ε / 2 := by field_simp
        linarith [h9, h6, h7, hnA]
      have hCK : 0 ≤ C₁ + K₂ := by linarith
      calc (C₁ + K₂) * (1 / m) * ‖((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖
          = (C₁ + K₂) * ((1 / m) * ‖((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖) := by ring
        _ ≤ (C₁ + K₂) * (nu γ * δ + ε / (2 * m)) := mul_le_mul_of_nonneg_left h5 hCK
        _ ≤ 1 / 8 := hsm
    have hb := hcore u τ (1 / m) _ _ hu h0 hs0 hF' hG' hsm'
    have hres' : ZM γ q M k π * hH γ q u M k π ((pc γ : ℂ) +
        (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) = _ := hres
    rw [hres']
    unfold phiH
    rw [Complex.exp_add, ← mul_sub]
    rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have he0 : 0 ≤ Real.exp (-ε * u) := (Real.exp_pos _).le
    calc Real.exp (-ε * u) * ‖_‖ ≤ Real.exp (-ε * u) *
          (B1 * (1 / m) * Real.exp (-(-ε / 2) * u) * Real.exp (-τ)) := by
          apply mul_le_mul_of_nonneg_left _ he0
          refine le_of_eq_of_le ?_ hb
          congr 1; ring
      _ = _ := by ring
  -- integrability on [0, σδ]
  have hIcc : Set.uIcc (0 : ℝ) (σ * δ) = Set.Icc 0 (σ * δ) := Set.uIcc_of_le hT0
  have hi1 : IntervalIntegrable (fun τ : ℝ => hH γ q u M k π ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) * exp ((θ : ℂ) * I))
      MeasureTheory.volume 0 (σ * δ) := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    apply ContinuousOn.mul _ continuousOn_const
    refine hcont.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro τ hτ
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact hzd τ hτ.1 hτ.2
    · intro hmem
      rw [Set.mem_singleton_iff] at hmem
      have h0 := ray_norm_ge (-ε / 2) θ τ hc hcos hsin hτ.1
      have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
      have h2 : (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ) = 0 := by
        linear_combination hmem
      have h3 : ((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I) = 0 := by
        rcases div_eq_zero_iff.1 h2 with h | h
        · exact h
        · exact absurd h hσc
      rw [h3, norm_zero] at h0; linarith
  have hi2 : IntervalIntegrable (fun τ : ℝ => phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
      MeasureTheory.volume 0 (σ * δ) := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact (phi_ray_contOn u (-ε / 2) θ k hc hcos hsin).mono (fun x hx => hx.1)
  have hsplitI := (intervalIntegral.integral_interval_add_Ioi
    (phi_ray_integrableOn u (-ε / 2) θ D U₀ k hc hcos hsin hD hu 0 le_rfl)
    (phi_ray_integrableOn u (-ε / 2) θ D U₀ k hc hcos hsin hD hu (σ * δ) hT0)).symm
  have hInt : (∫ τ in (0 : ℝ)..(σ * δ), (ZM γ q M k π * hH γ q u M k π ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
        ((Real.exp (-ε * u) : ℝ) : ℂ) * phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))) * exp ((θ : ℂ) * I)) =
      ZM γ q M k π * (∫ τ in (0 : ℝ)..(σ * δ), hH γ q u M k π ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) * exp ((θ : ℂ) * I)) -
        ((Real.exp (-ε * u) : ℝ) : ℂ) *
          ∫ τ in (0 : ℝ)..(σ * δ), phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hi1.const_mul _) (hi2.const_mul _)]
    congr 1; funext τ; ring
  have hX := interval_exp_bound (fun τ : ℝ => ZM γ q M k π * hH γ q u M k π ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
      ((Real.exp (-ε * u) : ℝ) : ℂ) * phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))) (σ * δ)
      (Real.exp (-ε * u) * (B1 * (1 / m) * Real.exp (-(-ε / 2) * u))) (exp ((θ : ℂ) * I))
      hT0 hw1 hpt (by positivity)
  have hY := phi_ray_tail u (-ε / 2) θ D U₀ k hc hcos hsin hD hu (σ * δ) hT0
  have hLHS : ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) * (((σ⁻¹ : ℝ) : ℂ) *
        ∫ τ in (0 : ℝ)..(σ * δ), hH γ q u M k π ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) * exp ((θ : ℂ) * I)) -
      ((Real.exp (-ε * u) / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ τ in Set.Ioi (0 : ℝ), phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ τ in (0 : ℝ)..(σ * δ), (ZM γ q M k π * hH γ q u M k π ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
          ((Real.exp (-ε * u) : ℝ) : ℂ) * phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))) * exp ((θ : ℂ) * I)) -
        ((Real.exp (-ε * u) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (σ * δ), phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) := by
    rw [hInt, hsplitI]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    generalize (∫ τ in (0 : ℝ)..(σ * δ), hH γ q u M k π ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) * exp ((θ : ℂ) * I)) = I1
    generalize (∫ τ in (0 : ℝ)..(σ * δ), phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) = I2
    generalize (∫ τ in Set.Ioi (σ * δ), phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) = I3
    push_cast
    field_simp
    ring
  rw [hLHS]
  generalize (∫ τ in (0 : ℝ)..(σ * δ), (ZM γ q M k π * hH γ q u M k π ((pc γ : ℂ) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
          ((Real.exp (-ε * u) : ℝ) : ℂ) * phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))) * exp ((θ : ℂ) * I)) = X at hX ⊢
  generalize (∫ τ in Set.Ioi (σ * δ), phiH u k (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) = Y at hY ⊢
  have hexpT : Real.exp (-(σ * δ)) ≤ 1 / (m * δ) := by
    have h1 : m * δ ≤ σ * δ := by
      have h0 : 1 * (m * δ) ≤ nu γ * (m * δ) := mul_le_mul_of_nonneg_right hν (by positivity)
      rw [hσ]; linarith
    have h2 : σ * δ + 1 ≤ Real.exp (σ * δ) := Real.add_one_le_exp _
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith
  have hEE : Real.exp (-ε * u) * Real.exp (-(-ε / 2) * u) = Real.exp (-(ε / 2) * u) := by
    rw [← Real.exp_add]; ring_nf
  have he0 : 0 ≤ Real.exp (-ε * u) := (Real.exp_pos _).le
  have hc0 : 0 ≤ Real.exp (-(-ε / 2) * u) := (Real.exp_pos _).le
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  have hY' : ‖Y‖ ≤ (2 / -(-ε / 2)) ^ k * Real.exp (D + (-ε / 2) ^ 3 / 3) *
      Real.exp (-(-ε / 2) * u) * (1 / (m * δ)) := by
    refine hY.trans ?_
    apply mul_le_mul_of_nonneg_left hexpT
    positivity
  calc ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (X - ((Real.exp (-ε * u) : ℝ) : ℂ) * Y)‖
      = 1 / (2 * Real.pi) * ‖X - ((Real.exp (-ε * u) : ℝ) : ℂ) * Y‖ := by
        rw [norm_mul, norm_real, Real.norm_of_nonneg hpi.le]
    _ ≤ 1 / (2 * Real.pi) * (‖X‖ + Real.exp (-ε * u) * ‖Y‖) := by
        apply mul_le_mul_of_nonneg_left _ hpi.le
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_real, Real.norm_of_nonneg he0]
    _ ≤ 1 / (2 * Real.pi) * (Real.exp (-ε * u) * (B1 * (1 / m) * Real.exp (-(-ε / 2) * u)) +
          Real.exp (-ε * u) * ((2 / -(-ε / 2)) ^ k * Real.exp (D + (-ε / 2) ^ 3 / 3) *
            Real.exp (-(-ε / 2) * u) * (1 / (m * δ)))) := by
        apply mul_le_mul_of_nonneg_left _ hpi.le
        exact add_le_add hX (mul_le_mul_of_nonneg_left hY' he0)
    _ = (B1 + (2 / -(-ε / 2)) ^ k * Real.exp (D + (-ε / 2) ^ 3 / 3) / δ) / (2 * Real.pi) *
          (Real.exp (-ε * u) * Real.exp (-(-ε / 2) * u)) / m := by
        field_simp
    _ = _ := by rw [hEE]

end P31E

open Complex MeasureTheory SpikedWishart.SoftEdge in
theorem solution :
    ∀ (ε U₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = 1 / 2 →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q u m σ : ℝ) (M : ℕ),
      U₀ ≤ u → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + ε / (2 * σ) ≤ δ₀ →
      (C₁ + K₂) * (nu γ * δ + ε / (2 * m)) ≤ 1 / 8 →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      ContinuousOn ((fun z : ℂ => exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) * (1 / (((pc γ : ℂ) - z) ^ k * gFn k π z)))) (Metric.closedBall (pc γ : ℂ) δ₀ \ {(pc γ : ℂ)}) →
      ‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (0 : ℝ)..δ, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * ((((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)) - q)) * exp ((M : ℂ) * fFn γ q (((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))) * (1 / (((pc γ : ℂ) - (((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))) ^ k * gFn k π (((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))))) * exp ((θ : ℂ) * I)) -
        ((Real.exp (-ε * u) / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (0 : ℝ), (exp (-(u : ℂ) * (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) * (1 / (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ k)) *
            exp ((θ : ℂ) * I)‖ ≤
        B * Real.exp (-(ε / 2) * u) / m := by
  exact P31E.near_ray
