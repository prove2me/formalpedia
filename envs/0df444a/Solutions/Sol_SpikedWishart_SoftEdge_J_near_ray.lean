-- Prove2me | solution 1 for SpikedWishart.SoftEdge.J_near_ray
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:48:44.783423+00:00
-- url     : https://prove2.me/submissions/dcbf2041-fcd3-4230-a59b-7e3f4ae67fe4

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option linter.all false
set_option Elab.async false

open Complex

namespace P31J
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


set_option maxHeartbeats 1000000 in
/-- J near core (BBP (148)-(152), `𝓙` side): on the ray `a = c + τ e^{iθ}` (`cos θ = -1/2`), if
`F` is within `K s ‖a‖⁴` of `-a³/3` and `G` within `K s ‖a‖` of `1`, and `K s ‖a‖ ≤ 1/8`, then
`e^{va}(e^F G - e^{-a³/3}) a^k` is at most `B s e^{cv} e^{-τ}`, uniformly for `v ≥ V₀`. -/
theorem near_coreJ (c θ V₀ K : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = -(1 / 2))
    (hsin : Real.sin θ ^ 2 = 3 / 4) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (v τ s : ℝ) (F G : ℂ), V₀ ≤ v → 0 ≤ τ → 0 ≤ s →
      ‖F - -(((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3)‖ ≤
        K * s * ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 4 →
      ‖G - 1‖ ≤ K * s * ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ →
      K * s * ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤ 1 / 8 →
      ‖exp ((v : ℂ) * ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))) *
          (exp F * G - exp (-(((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3))) *
          ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ k‖ ≤
        B * s * Real.exp (c * v) * Real.exp (-τ) := by
  obtain ⟨D, hD⟩ := cubic_bound (2 * (-V₀ / 2 + c ^ 2 / 2 + 3 * c ^ 2 / 8 + 5 + (k : ℝ)))
    (4 * (c / 2 - 3 * c / 8))
  refine ⟨5 * K * Real.exp (D - c ^ 3 / 3 - c ^ 3 / 8 - 4 * c - (k : ℝ) * c), by positivity,
    fun v τ s F G hv hτ hs hF hG hsm => ?_⟩
  set a : ℂ := (c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I) with ha
  set n : ℝ := ‖a‖ with hn
  have hre : a.re = c - τ / 2 := by
    rw [ha, Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im, hcos]; ring
  have him : a.im = τ * Real.sin θ := by
    rw [ha, Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]; ring
  have him2 : a.im ^ 2 = 3 / 4 * τ ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hn0 : 0 ≤ n := norm_nonneg a
  have hnhi : n ≤ τ - c := by
    have h1 := norm_add_le (c : ℂ) ((τ : ℂ) * exp ((θ : ℂ) * I))
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real, Real.norm_of_nonneg hτ,
      Real.norm_eq_abs, abs_of_neg hc] at h1
    rw [hn, ha]; linarith only [h1]
  have hE1 : ‖exp ((v : ℂ) * a)‖ = Real.exp (v * (c - τ / 2)) := by
    rw [Complex.norm_exp]; congr 1
    rw [Complex.mul_re, ofReal_re, ofReal_im, hre]; ring
  have hE3 : ‖a ^ k‖ ≤ Real.exp ((k : ℝ) * (τ - c)) := by
    rw [norm_pow, ← hn]
    have h1 : n ≤ Real.exp n := by linarith [Real.add_one_le_exp n]
    have h2 : n ^ k ≤ Real.exp n ^ k := pow_le_pow_left₀ hn0 h1 k
    rw [← Real.exp_nat_mul] at h2
    refine h2.trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_left hnhi (Nat.cast_nonneg k)
  have hreA : (-(a ^ 3 / 3)).re = -c ^ 3 / 3 + c ^ 2 / 2 * τ + c / 2 * τ ^ 2 - τ ^ 3 / 3 := by
    have : (-(a ^ 3 / 3) : ℂ) = ((-1 / 3 : ℝ) : ℂ) * a ^ 3 := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
    have hc3 : (a ^ 3).re = a.re ^ 3 - 3 * a.re * a.im ^ 2 := by
      rw [show a ^ 3 = a * a * a by ring, Complex.mul_re, Complex.mul_re, Complex.mul_im]; ring
    rw [hc3, him2, hre]; ring
  set x : ℂ := F - -(a ^ 3 / 3) with hx
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
    rw [norm_one] at this; linarith only [hG, hsm, this]
  have hsplit : exp F * G - exp (-(a ^ 3 / 3)) =
      exp (-(a ^ 3 / 3)) * ((exp x - 1) * G + (G - 1)) := by
    have : F = -(a ^ 3 / 3) + x := by rw [hx]; ring
    rw [this, Complex.exp_add]; ring
  have hexA : ‖exp (-(a ^ 3 / 3))‖ =
      Real.exp (-c ^ 3 / 3 + c ^ 2 / 2 * τ + c / 2 * τ ^ 2 - τ ^ 3 / 3) := by
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
            mul_le_mul (by linarith only [hxK]) hexx (by positivity) (by positivity)
          have h2 : K * s * n ≤ K * s * n * Real.exp (n ^ 3 / 8) := le_mul_of_one_le_right hKsn hen
          linarith only [h1, h2]
      _ = K * s * (4 * n ^ 4 + n) * Real.exp (n ^ 3 / 8) := by ring
  have hpoly : 4 * n ^ 4 + n ≤ 5 * Real.exp (4 * (τ - c)) := by
    have h1 : 1 + n ≤ Real.exp n := by linarith [Real.add_one_le_exp n]
    have h2 : (1 + n) ^ 4 ≤ Real.exp n ^ 4 := pow_le_pow_left₀ (by linarith only [hn0]) h1 4
    rw [← Real.exp_nat_mul] at h2
    have h3 : Real.exp ((4 : ℕ) * n) ≤ Real.exp (4 * (τ - c)) := by
      rw [Real.exp_le_exp]; push_cast; linarith only [hnhi]
    have h4 : 4 * n ^ 4 + n ≤ 5 * (1 + n) ^ 4 := by nlinarith [pow_nonneg hn0 2, pow_nonneg hn0 3]
    linarith only [h2, h3, h4]
  have hn3 : n ^ 3 ≤ (τ - c) ^ 3 := pow_le_pow_left₀ hn0 hnhi 3
  have hD' := hD (τ / 2) (by linarith only [hτ])
  have hexp_total : Real.exp (v * (c - τ / 2)) *
      (Real.exp (-c ^ 3 / 3 + c ^ 2 / 2 * τ + c / 2 * τ ^ 2 - τ ^ 3 / 3) *
        (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c)))) * Real.exp ((k : ℝ) * (τ - c)) ≤
      Real.exp (D - c ^ 3 / 3 - c ^ 3 / 8 - 4 * c - (k : ℝ) * c) * Real.exp (c * v) *
        Real.exp (-τ) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add, Real.exp_le_exp]
    have hu' : -v * (τ / 2) ≤ -V₀ * (τ / 2) := by nlinarith
    have ht3 : 0 ≤ τ ^ 3 := pow_nonneg hτ 3
    have hc3 : (τ - c) ^ 3 = τ ^ 3 - 3 * c * τ ^ 2 + 3 * c ^ 2 * τ - c ^ 3 := by ring
    linarith only [hu', hn3, hD', ht3]
  rw [norm_mul, norm_mul, hE1, hsplit, norm_mul, hexA]
  have hmid' : ‖(exp x - 1) * G + (G - 1)‖ ≤
      5 * K * s * (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c))) := by
    calc ‖(exp x - 1) * G + (G - 1)‖ ≤ K * s * (4 * n ^ 4 + n) * Real.exp (n ^ 3 / 8) := hmid
      _ ≤ K * s * (5 * Real.exp (4 * (τ - c))) * Real.exp (n ^ 3 / 8) := by
          gcongr
      _ = 5 * K * s * (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c))) := by ring
  calc Real.exp (v * (c - τ / 2)) *
        (Real.exp (-c ^ 3 / 3 + c ^ 2 / 2 * τ + c / 2 * τ ^ 2 - τ ^ 3 / 3) *
          ‖(exp x - 1) * G + (G - 1)‖) * ‖a ^ k‖
      ≤ Real.exp (v * (c - τ / 2)) *
        (Real.exp (-c ^ 3 / 3 + c ^ 2 / 2 * τ + c / 2 * τ ^ 2 - τ ^ 3 / 3) *
          (5 * K * s * (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c))))) *
          Real.exp ((k : ℝ) * (τ - c)) := by
        gcongr
    _ = 5 * K * s * (Real.exp (v * (c - τ / 2)) *
        (Real.exp (-c ^ 3 / 3 + c ^ 2 / 2 * τ + c / 2 * τ ^ 2 - τ ^ 3 / 3) *
          (Real.exp (n ^ 3 / 8) * Real.exp (4 * (τ - c)))) * Real.exp ((k : ℝ) * (τ - c))) := by
        ring
    _ ≤ 5 * K * s * (Real.exp (D - c ^ 3 / 3 - c ^ 3 / 8 - 4 * c - (k : ℝ) * c) *
          Real.exp (c * v) * Real.exp (-τ)) := by
        gcongr
    _ = 5 * K * Real.exp (D - c ^ 3 / 3 - c ^ 3 / 8 - 4 * c - (k : ℝ) * c) * s *
          Real.exp (c * v) * Real.exp (-τ) := by ring

/-- The `𝓙_∞` integrand (BBP (122)). -/
noncomputable def phiJ (v : ℝ) (k : ℕ) (a : ℂ) : ℂ := exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k

theorem re_cube (a : ℂ) : (a ^ 3).re = a.re ^ 3 - 3 * a.re * a.im ^ 2 := by
  rw [show a ^ 3 = a * a * a by ring, Complex.mul_re, Complex.mul_re, Complex.mul_im]; ring

theorem ray_norm_le (c θ τ : ℝ) (hc : c < 0) (hτ : 0 ≤ τ) :
    ‖(c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤ τ - c := by
  have h1 := norm_add_le (c : ℂ) ((τ : ℂ) * exp ((θ : ℂ) * I))
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real, Real.norm_of_nonneg hτ,
    Real.norm_eq_abs, abs_of_neg hc] at h1
  linarith only [h1]

/-- Pointwise bound for the `𝓙_∞` ray integrand (`cos θ = -1/2`, vertex `c < 0`). -/
theorem J_integrand_bound (c x0 θ D : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = -(1 / 2))
    (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + (k : ℝ) + 1) * t + (c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (v : ℝ) (hv : x0 ≤ v) (t : ℝ) (ht : 0 ≤ t) :
    ‖phiJ v k ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤
      (Real.exp (D - c ^ 3 / 3 - (k : ℝ) * c) * Real.exp (c * v)) * Real.exp (-t) := by
  set a : ℂ := (c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  have hre : a.re = c - t / 2 := by
    rw [ha, Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im, hcos]; ring
  have him : a.im = t * Real.sin θ := by
    rw [ha, Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]; ring
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hwre : ((v : ℂ) * a - a ^ 3 / 3).re =
      v * c - v * t / 2 - c ^ 3 / 3 + c ^ 2 / 2 * t + c / 2 * t ^ 2 - t ^ 3 / 3 := by
    rw [Complex.sub_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, ofReal_re, ofReal_im,
      him2, hre]
    ring
  have hn0 : 0 ≤ ‖a‖ := norm_nonneg a
  have hnhi : ‖a‖ ≤ t - c := ray_norm_le c θ t hc ht
  have hk : ‖a ^ k‖ ≤ Real.exp ((k : ℝ) * (t - c)) := by
    rw [norm_pow]
    have h1 : ‖a‖ ≤ Real.exp ‖a‖ := by linarith [Real.add_one_le_exp ‖a‖]
    have h2 : ‖a‖ ^ k ≤ Real.exp ‖a‖ ^ k := pow_le_pow_left₀ hn0 h1 k
    rw [← Real.exp_nat_mul] at h2
    exact h2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnhi (Nat.cast_nonneg k)))
  have hexp : ((v : ℂ) * a - a ^ 3 / 3).re + (k : ℝ) * (t - c) ≤
      D - c ^ 3 / 3 - (k : ℝ) * c + c * v + -t := by
    rw [hwre]
    have h1 := hD t ht
    have h2 : x0 * t ≤ v * t := mul_le_mul_of_nonneg_right hv ht
    linarith only [h1, h2]
  unfold phiJ
  rw [norm_mul, norm_exp]
  calc Real.exp ((v : ℂ) * a - a ^ 3 / 3).re * ‖a ^ k‖
      ≤ Real.exp ((v : ℂ) * a - a ^ 3 / 3).re * Real.exp ((k : ℝ) * (t - c)) :=
        mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    _ = Real.exp (((v : ℂ) * a - a ^ 3 / 3).re + (k : ℝ) * (t - c)) := by rw [Real.exp_add]
    _ ≤ Real.exp (D - c ^ 3 / 3 - (k : ℝ) * c + c * v + -t) := Real.exp_le_exp.mpr hexp
    _ = (Real.exp (D - c ^ 3 / 3 - (k : ℝ) * c) * Real.exp (c * v)) * Real.exp (-t) := by
        rw [Real.exp_add, Real.exp_add]

theorem phiJ_ray_cont (v c θ : ℝ) (k : ℕ) :
    Continuous (fun τ : ℝ => phiJ v k ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
      exp ((θ : ℂ) * I)) := by
  unfold phiJ; fun_prop

theorem phiJ_ray_integrableOn (v c θ D x0 : ℝ) (k : ℕ) (hc : c < 0)
    (hcos : Real.cos θ = -(1 / 2)) (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + (k : ℝ) + 1) * t + (c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (hv : x0 ≤ v) (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun τ : ℝ => phiJ v k ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
      exp ((θ : ℂ) * I)) (Set.Ioi T) := by
  have hg : Integrable (fun τ : ℝ => (Real.exp (D - c ^ 3 / 3 - (k : ℝ) * c) *
      Real.exp (c * v)) * Real.exp (-τ)) (volume.restrict (Set.Ioi T)) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi T) _
  refine Integrable.mono' hg ?_ ?_
  · exact (phiJ_ray_cont v c θ k).continuousOn.aestronglyMeasurable measurableSet_Ioi
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    exact J_integrand_bound c x0 θ D k hc hcos hsin hD v hv t (hT.trans (le_of_lt ht))

theorem phiJ_ray_tail (v c θ D x0 : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = -(1 / 2))
    (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + (k : ℝ) + 1) * t + (c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (hv : x0 ≤ v) (T : ℝ) (hT : 0 ≤ T) :
    ‖∫ τ in Set.Ioi T, phiJ v k ((c : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤
      (Real.exp (D - c ^ 3 / 3 - (k : ℝ) * c) * Real.exp (c * v)) * Real.exp (-T) := by
  have hg : Integrable (fun τ : ℝ => (Real.exp (D - c ^ 3 / 3 - (k : ℝ) * c) *
      Real.exp (c * v)) * Real.exp (-τ)) (volume.restrict (Set.Ioi T)) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi T) _
  calc _ ≤ ∫ τ in Set.Ioi T, (Real.exp (D - c ^ 3 / 3 - (k : ℝ) * c) *
        Real.exp (c * v)) * Real.exp (-τ) := by
        apply norm_integral_le_of_norm_le hg
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall (fun t ht => ?_)
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
        exact J_integrand_bound c x0 θ D k hc hcos hsin hD v hv t (hT.trans (le_of_lt ht))
    _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi]

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

set_option maxHeartbeats 2000000 in
/-- J-near for one ray of `Σ*` (BBP (148)-(152), `𝓙` side): the rescaled near ray of `𝓙/Z_M`
versus the full ray of `𝓙_∞` with vertex `-2ε`; error `B e^{-εv}/m`, `m = M^{1/3}`. -/
theorem near_rayJ (ε V₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ) (hε : 0 < ε) (hcos : Real.cos θ = -(1 / 2))
    (hsin : Real.sin θ ^ 2 = 3 / 4) (hC₁ : 0 ≤ C₁) (hK₂ : 0 ≤ K₂) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + 2 * ε / σ ≤ δ₀ →
      (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      gFn k π (pc γ) ≠ 0 →
      ContinuousOn (hJ γ q v M k π) (Metric.closedBall (pc γ : ℂ) δ₀) →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (0 : ℝ)..δ, hJ γ q v M k π (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) -
        ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (0 : ℝ), phiJ v k (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
            exp ((θ : ℂ) * I)‖ ≤
        B * Real.exp (-ε * v) / m := by
  have hc : -2 * ε < 0 := by linarith only [hε]
  obtain ⟨B1, hB1, hcore⟩ := near_coreJ (-2 * ε) θ V₀ (C₁ + 2 * K₂) k hc hcos hsin (by linarith only [hC₁, hK₂])
  obtain ⟨D, hD⟩ := cubic_bound (-V₀ / 2 + (-2 * ε) ^ 2 / 2 + (k : ℝ) + 1) ((-2 * ε) / 2)
  have hKT : 0 ≤ Real.exp (D - (-2 * ε) ^ 3 / 3 - (k : ℝ) * (-2 * ε)) := (Real.exp_pos _).le
  refine ⟨(B1 + Real.exp (D - (-2 * ε) ^ 3 / 3 - (k : ℝ) * (-2 * ε)) / δ) / (2 * Real.pi),
    by positivity, ?_⟩
  intro r π γ q v m σ M hv hm1 hm3 hν hσdef hσ hq hδ0 hsm hTay hGr hg0 hcont
  have hm0 : 0 < m := by linarith only [hm1]
  have hν0 : 0 < nu γ := by linarith only [hν]
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have hT0 : 0 ≤ σ * δ := by positivity
  have hw1 : ‖exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  rw [ray_rescale (hJ γ q v M k π) (pc γ) (-2 * ε) σ δ (exp ((θ : ℂ) * I)) hσ0]
  have hzd : ∀ τ : ℝ, 0 ≤ τ → τ ≤ σ * δ →
      ‖(pc γ : ℂ) + (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ) - pc γ‖ ≤ δ₀ := by
    intro τ h0 h1
    rw [add_sub_cancel_left, norm_div, norm_real, Real.norm_of_nonneg hσ0.le, div_le_iff₀ hσ0]
    have h2 := ray_norm_le (-2 * ε) θ τ hc h0
    have h3 : (δ + 2 * ε / σ) * σ ≤ δ₀ * σ := mul_le_mul_of_nonneg_right hδ0 hσ0.le
    have h4 : (δ + 2 * ε / σ) * σ = σ * δ + 2 * ε := by field_simp
    linarith only [h1, h2, h3, h4]
  have hpt : ∀ τ : ℝ, 0 ≤ τ → τ ≤ σ * δ →
      ‖(ZM γ q M k π)⁻¹ * hJ γ q v M k π
          ((pc γ : ℂ) + (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
        ((Real.exp (ε * v) : ℝ) : ℂ) *
          phiJ v k (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))‖ ≤
      (Real.exp (ε * v) * (B1 * (1 / m) * Real.exp (-2 * ε * v))) * Real.exp (-τ) := by
    intro τ h0 h1
    have hd := hzd τ h0 h1
    obtain ⟨hg0z, hGb⟩ := hGr _ hd
    have hTb := hTay _ hd
    have hres := rescale_ptJ γ q ε v σ M k π
      ((pc γ : ℂ) + (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) hσ0 hσdef hq hg0
    have hsa : (σ : ℂ) * ((pc γ : ℂ) +
        (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ) - pc γ) =
        ((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I) := by
      field_simp; ring
    rw [hsa] at hres
    have hF := F_scale γ q m σ C₁ M _ hm0 hm3 hν hσ hC₁ hTb
    have hG := G_scale γ K₂ m σ _ _ hm0 hν hσ hK₂ hGb
    have hnA := ray_norm_le (-2 * ε) θ τ hc h0
    have hn0 := norm_nonneg (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I))
    have hs0 : 0 ≤ 1 / m := by positivity
    have h5 : (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤
        nu γ * δ + 2 * ε / m := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm0]
      have h6 : τ - -2 * ε ≤ σ * δ + 2 * ε := by linarith only [h1]
      have h7 : σ * δ = nu γ * δ * m := by rw [hσ]; ring
      have h9 : (nu γ * δ + 2 * ε / m) * m = nu γ * δ * m + 2 * ε := by field_simp
      linarith only [hnA, h6, h7, h9]
    have hCK : 0 ≤ C₁ + 2 * K₂ := by linarith only [hC₁, hK₂]
    have hsm' : (C₁ + 2 * K₂) * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤
        1 / 8 := by
      calc (C₁ + 2 * K₂) * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖
          = (C₁ + 2 * K₂) * ((1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖) := by
            ring
        _ ≤ (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) := mul_le_mul_of_nonneg_left h5 hCK
        _ ≤ 1 / 8 := hsm
    have hX0 : 0 ≤ (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ := by positivity
    have hF' : ‖-(M : ℂ) * (fFn γ q ((pc γ : ℂ) +
        (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) - fFn γ q (pc γ)) -
        -((((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3)‖ ≤
        (C₁ + 2 * K₂) * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 4 := by
      rw [show ∀ X Y : ℂ, -(M : ℂ) * X - -Y = -((M : ℂ) * X - Y) from fun X Y => by ring,
        norm_neg]
      refine hF.trans ?_
      have : 0 ≤ (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 4 := by
        positivity
      nlinarith
    have hη : K₂ * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤ 1 / 2 := by
      have : K₂ * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ ≤
          (C₁ + 2 * K₂) * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ := by
        have e1 : K₂ * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ =
            K₂ * ((1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖) := by ring
        have e2 : (C₁ + 2 * K₂) * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ =
            (C₁ + 2 * K₂) * ((1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖) := by
          ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right (by linarith only [hC₁, hK₂]) hX0
      linarith only [hsm', this]
    obtain ⟨-, hGinv⟩ := inv_ratio _ _ hG hη
    rw [inv_div] at hGinv
    have hG' : ‖gFn k π ((pc γ : ℂ) +
        (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) / gFn k π (pc γ) - 1‖ ≤
        (C₁ + 2 * K₂) * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ := by
      refine hGinv.trans ?_
      have e1 : 2 * (K₂ * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖) =
          (2 * K₂) * ((1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖) := by ring
      have e2 : (C₁ + 2 * K₂) * (1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖ =
          (C₁ + 2 * K₂) * ((1 / m) * ‖((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)‖) := by
        ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (by linarith only [hC₁]) hX0
    have hb := hcore v τ (1 / m) _ _ hv h0 hs0 hF' hG' hsm'
    rw [hres]
    unfold phiJ
    rw [sub_eq_add_neg ((v : ℂ) * (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)))
      ((((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3), Complex.exp_add, ← mul_sub]
    rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have he0 : 0 ≤ Real.exp (ε * v) := (Real.exp_pos _).le
    calc Real.exp (ε * v) * ‖_‖ ≤ Real.exp (ε * v) *
          (B1 * (1 / m) * Real.exp (-2 * ε * v) * Real.exp (-τ)) := by
          apply mul_le_mul_of_nonneg_left _ he0
          refine le_of_eq_of_le ?_ hb
          congr 1; ring
      _ = _ := by ring
  have hIcc : Set.uIcc (0 : ℝ) (σ * δ) = Set.Icc 0 (σ * δ) := Set.uIcc_of_le hT0
  have hi1 : IntervalIntegrable (fun τ : ℝ => hJ γ q v M k π ((pc γ : ℂ) +
      (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) * exp ((θ : ℂ) * I))
      MeasureTheory.volume 0 (σ * δ) := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    apply ContinuousOn.mul _ continuousOn_const
    refine hcont.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro τ hτ
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hzd τ hτ.1 hτ.2
  have hi2 : IntervalIntegrable (fun τ : ℝ => phiJ v k (((-2 * ε : ℝ) : ℂ) +
      (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) MeasureTheory.volume 0 (σ * δ) :=
    (phiJ_ray_cont v (-2 * ε) θ k).intervalIntegrable _ _
  have hsplitI := (intervalIntegral.integral_interval_add_Ioi
    (phiJ_ray_integrableOn v (-2 * ε) θ D V₀ k hc hcos hsin hD hv 0 le_rfl)
    (phiJ_ray_integrableOn v (-2 * ε) θ D V₀ k hc hcos hsin hD hv (σ * δ) hT0)).symm
  have hInt : (∫ τ in (0 : ℝ)..(σ * δ), ((ZM γ q M k π)⁻¹ * hJ γ q v M k π ((pc γ : ℂ) +
        (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
        ((Real.exp (ε * v) : ℝ) : ℂ) * phiJ v k (((-2 * ε : ℝ) : ℂ) +
          (τ : ℂ) * exp ((θ : ℂ) * I))) * exp ((θ : ℂ) * I)) =
      (ZM γ q M k π)⁻¹ * (∫ τ in (0 : ℝ)..(σ * δ), hJ γ q v M k π ((pc γ : ℂ) +
        (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) * exp ((θ : ℂ) * I)) -
        ((Real.exp (ε * v) : ℝ) : ℂ) *
          ∫ τ in (0 : ℝ)..(σ * δ), phiJ v k (((-2 * ε : ℝ) : ℂ) +
            (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hi1.const_mul _) (hi2.const_mul _)]
    congr 1; funext τ; ring
  have hX := interval_exp_bound (fun τ : ℝ => (ZM γ q M k π)⁻¹ * hJ γ q v M k π ((pc γ : ℂ) +
      (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
      ((Real.exp (ε * v) : ℝ) : ℂ) * phiJ v k (((-2 * ε : ℝ) : ℂ) +
        (τ : ℂ) * exp ((θ : ℂ) * I))) (σ * δ)
      (Real.exp (ε * v) * (B1 * (1 / m) * Real.exp (-2 * ε * v))) (exp ((θ : ℂ) * I))
      hT0 hw1 hpt (by positivity)
  have hY := phiJ_ray_tail v (-2 * ε) θ D V₀ k hc hcos hsin hD hv (σ * δ) hT0
  have hLHS : (ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) * (((σ⁻¹ : ℝ) : ℂ) *
        ∫ τ in (0 : ℝ)..(σ * δ), hJ γ q v M k π ((pc γ : ℂ) +
          (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) * exp ((θ : ℂ) * I)) -
      ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ τ in Set.Ioi (0 : ℝ), phiJ v k (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
          exp ((θ : ℂ) * I) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ τ in (0 : ℝ)..(σ * δ), ((ZM γ q M k π)⁻¹ * hJ γ q v M k π ((pc γ : ℂ) +
          (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
          ((Real.exp (ε * v) : ℝ) : ℂ) * phiJ v k (((-2 * ε : ℝ) : ℂ) +
            (τ : ℂ) * exp ((θ : ℂ) * I))) * exp ((θ : ℂ) * I)) -
        ((Real.exp (ε * v) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (σ * δ), phiJ v k (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
            exp ((θ : ℂ) * I)) := by
    rw [hInt, hsplitI]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    generalize (∫ τ in (0 : ℝ)..(σ * δ), hJ γ q v M k π ((pc γ : ℂ) +
      (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) * exp ((θ : ℂ) * I)) = I1
    generalize (∫ τ in (0 : ℝ)..(σ * δ), phiJ v k (((-2 * ε : ℝ) : ℂ) +
      (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) = I2
    generalize (∫ τ in Set.Ioi (σ * δ), phiJ v k (((-2 * ε : ℝ) : ℂ) +
      (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) = I3
    push_cast
    field_simp
    ring
  rw [hLHS]
  generalize (∫ τ in (0 : ℝ)..(σ * δ), ((ZM γ q M k π)⁻¹ * hJ γ q v M k π ((pc γ : ℂ) +
      (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) / (σ : ℂ)) -
      ((Real.exp (ε * v) : ℝ) : ℂ) * phiJ v k (((-2 * ε : ℝ) : ℂ) +
        (τ : ℂ) * exp ((θ : ℂ) * I))) * exp ((θ : ℂ) * I)) = X at hX ⊢
  generalize (∫ τ in Set.Ioi (σ * δ), phiJ v k (((-2 * ε : ℝ) : ℂ) +
      (τ : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) = Y at hY ⊢
  have hexpT : Real.exp (-(σ * δ)) ≤ 1 / (m * δ) := by
    have h1 : m * δ ≤ σ * δ := by
      have h0 : 1 * (m * δ) ≤ nu γ * (m * δ) := mul_le_mul_of_nonneg_right hν (by positivity)
      rw [hσ]; linarith only [h0]
    have h2 : σ * δ + 1 ≤ Real.exp (σ * δ) := Real.add_one_le_exp _
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith only [h1, h2]
  have hEE : Real.exp (ε * v) * Real.exp (-2 * ε * v) = Real.exp (-ε * v) := by
    rw [← Real.exp_add]; ring_nf
  have he0 : 0 ≤ Real.exp (ε * v) := (Real.exp_pos _).le
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  have hY' : ‖Y‖ ≤ Real.exp (D - (-2 * ε) ^ 3 / 3 - (k : ℝ) * (-2 * ε)) *
      Real.exp (-2 * ε * v) * (1 / (m * δ)) := by
    refine hY.trans ?_
    apply mul_le_mul_of_nonneg_left hexpT
    positivity
  calc ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (X - ((Real.exp (ε * v) : ℝ) : ℂ) * Y)‖
      = 1 / (2 * Real.pi) * ‖X - ((Real.exp (ε * v) : ℝ) : ℂ) * Y‖ := by
        rw [norm_mul, norm_real, Real.norm_of_nonneg hpi.le]
    _ ≤ 1 / (2 * Real.pi) * (‖X‖ + Real.exp (ε * v) * ‖Y‖) := by
        apply mul_le_mul_of_nonneg_left _ hpi.le
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_real, Real.norm_of_nonneg he0]
    _ ≤ 1 / (2 * Real.pi) * (Real.exp (ε * v) * (B1 * (1 / m) * Real.exp (-2 * ε * v)) +
          Real.exp (ε * v) * (Real.exp (D - (-2 * ε) ^ 3 / 3 - (k : ℝ) * (-2 * ε)) *
            Real.exp (-2 * ε * v) * (1 / (m * δ)))) := by
        apply mul_le_mul_of_nonneg_left _ hpi.le
        exact add_le_add hX (mul_le_mul_of_nonneg_left hY' he0)
    _ = (B1 + Real.exp (D - (-2 * ε) ^ 3 / 3 - (k : ℝ) * (-2 * ε)) / δ) / (2 * Real.pi) *
          (Real.exp (ε * v) * Real.exp (-2 * ε * v)) / m := by
        field_simp
    _ = _ := by rw [hEE]

end P31J

open Complex MeasureTheory SpikedWishart.SoftEdge in
theorem solution :
    ∀ (ε V₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = -(1 / 2) →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + 2 * ε / σ ≤ δ₀ →
      (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      gFn k π (pc γ) ≠ 0 →
      ContinuousOn ((fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) * (((pc γ : ℂ) - z) ^ k * gFn k π z))) (Metric.closedBall (pc γ : ℂ) δ₀) →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (0 : ℝ)..δ, (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * ((((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)) - q)) * exp (-(M : ℂ) * fFn γ q (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))) * (((pc γ : ℂ) - (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))) ^ k * gFn k π (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)))) * exp ((θ : ℂ) * I)) -
        ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (0 : ℝ), (exp ((v : ℂ) * (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) - (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) * (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ k) *
            exp ((θ : ℂ) * I)‖ ≤
        B * Real.exp (-ε * v) / m := by
  exact P31J.near_rayJ
