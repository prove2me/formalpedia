-- Prove2me | solution 1 for SpikedWishart.SoftEdge.eq_200_k_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T09:19:54.923097+00:00
-- url     : https://prove2.me/submissions/2ac8fe57-8689-4906-a217-48868edd5489

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option autoImplicit false

namespace Lib5e

open MeasureTheory Filter Topology Set Complex

/-- A cubic with leading coefficient `-1/3` is bounded above on `[0, ∞)`. -/
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
    linarith
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


open SpikedWishart.SoftEdge

/-- Rotation of a broken-line contour by `ω`. -/
theorem rayIntegral_rotate (ψ : ℂ → ℂ) (c ω : ℂ) (θin θout θin' θout' : ℝ)
    (hin : exp ((θin' : ℂ) * I) = ω * exp ((θin : ℂ) * I))
    (hout : exp ((θout' : ℂ) * I) = ω * exp ((θout : ℂ) * I)) :
    rayIntegral (ω * c) θin' θout' ψ = ω * rayIntegral c θin θout (fun a => ψ (ω * a)) := by
  unfold rayIntegral
  rw [hin, hout, mul_sub, ← integral_const_mul, ← integral_const_mul]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    show ψ (ω * c + (t : ℂ) * (ω * exp ((θout : ℂ) * I))) * (ω * exp ((θout : ℂ) * I)) =
      ω * (ψ (ω * (c + (t : ℂ) * exp ((θout : ℂ) * I))) * exp ((θout : ℂ) * I))
    rw [show ω * c + (t : ℂ) * (ω * exp ((θout : ℂ) * I)) =
      ω * (c + (t : ℂ) * exp ((θout : ℂ) * I)) by ring]
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    show ψ (ω * c + (t : ℂ) * (ω * exp ((θin : ℂ) * I))) * (ω * exp ((θin : ℂ) * I)) =
      ω * (ψ (ω * (c + (t : ℂ) * exp ((θin : ℂ) * I))) * exp ((θin : ℂ) * I))
    rw [show ω * c + (t : ℂ) * (ω * exp ((θin : ℂ) * I)) =
      ω * (c + (t : ℂ) * exp ((θin : ℂ) * I)) by ring]
    ring

/-- Derivative of one ray integral in its (real) vertex: `d/ds ∫₀^∞ φ(s + tω) ω dt = -φ(s)`. -/
theorem ray_deriv (φ φ' : ℂ → ℂ) (hφ : ∀ z, HasDerivAt φ (φ' z) z) (hφ'c : Continuous φ') (θ : ℝ)
    (hb : ∀ R : ℝ, ∃ B : ℝ, ∀ s : ℝ, |s| ≤ R → ∀ t : ℝ, 0 < t →
      ‖φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t)) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in Ioi (0 : ℝ),
      φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) (-φ s0) s0 := by
  obtain ⟨B, hB⟩ := hb (|s0| + 1)
  have hcont : Continuous φ := continuous_iff_continuousAt.2 fun z => (hφ z).continuousAt
  have hω : ‖exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  have hline : ∀ s : ℝ, Continuous fun t : ℝ => (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) :=
    fun s => continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hbi : Integrable (fun t : ℝ => B * Real.exp (-t)) (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) B
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℝ) (t : ℝ) => φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
    (F' := fun (s : ℝ) (t : ℝ) => φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
    (x₀ := s0) (bound := fun t => B * Real.exp (-t)) (s := Metric.ball s0 1) (Metric.ball_mem_nhds s0 one_pos)
    (Filter.Eventually.of_forall (fun s => ((hcont.comp (hline s)).mul continuous_const).aestronglyMeasurable))
    (by
      refine hbi.mono' ((hcont.comp (hline s0)).mul continuous_const).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [norm_mul, hω, mul_one]
      exact (hB s0 (by linarith) t ht).1)
    (((hφ'c.comp (hline s0)).mul continuous_const).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht s hs => ?_)
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have hs' : |s| ≤ |s0| + 1 := by
        have := abs_sub_abs_le_abs_sub s s0
        linarith
      show ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B * Real.exp (-t)
      rw [norm_mul, hω, mul_one]
      exact (hB s hs' t ht).2)
    hbi
    (by
      refine Filter.Eventually.of_forall (fun t s _ => ?_)
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) 1 s :=
        ((hasDerivAt_id' (s : ℂ)).comp_ofReal).add_const _
      have h2 := ((hφ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))).comp s h1).mul_const (exp ((θ : ℂ) * I))
      rw [mul_one] at h2
      exact h2)
  have hval : ∫ t in Ioi (0 : ℝ), φ' ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I) =
      -φ s0 := by
    have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => φ ((s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I)))
        (φ' ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) t := by
      intro t _
      have h1 : HasDerivAt (fun y : ℝ => (s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I)) (exp ((θ : ℂ) * I)) t := by
        have := (((hasDerivAt_id' (t : ℂ)).comp_ofReal).mul_const (exp ((θ : ℂ) * I))).const_add (s0 : ℂ)
        rw [one_mul] at this
        exact this
      exact (hφ _).comp t h1
    have hlim : Tendsto (fun y : ℝ => φ ((s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hE : Tendsto (fun y : ℝ => B * Real.exp (-y)) atTop (𝓝 0) := by
        simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul B)
      refine squeeze_zero' (Filter.Eventually.of_forall (fun y => norm_nonneg _)) ?_ hE
      filter_upwards [Filter.eventually_gt_atTop 0] with y hy
      exact (hB s0 (by linarith) y hy).1
    have := integral_Ioi_of_hasDerivAt_of_tendsto
      ((hcont.comp (hline s0)).continuousWithinAt) hd key.1 hlim
    rw [this]
    simp
  rw [← hval]
  exact key.2

/-- The broken-line integral does not depend on its real vertex. -/
theorem rayIntegral_vertex_indep (φ φ' : ℂ → ℂ) (hφ : ∀ z, HasDerivAt φ (φ' z) z)
    (hφ'c : Continuous φ') (θin θout : ℝ)
    (hbin : ∀ R : ℝ, ∃ B : ℝ, ∀ s : ℝ, |s| ≤ R → ∀ t : ℝ, 0 < t →
      ‖φ ((s : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I))‖ ≤ B * Real.exp (-t))
    (hbout : ∀ R : ℝ, ∃ B : ℝ, ∀ s : ℝ, |s| ≤ R → ∀ t : ℝ, 0 < t →
      ‖φ ((s : ℂ) + (t : ℂ) * exp ((θout : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θout : ℂ) * I))‖ ≤ B * Real.exp (-t)) (p : ℝ) :
    rayIntegral (p : ℂ) θin θout φ = rayIntegral 0 θin θout φ := by
  have hD : ∀ s : ℝ, HasDerivAt (fun s : ℝ => rayIntegral (s : ℂ) θin θout φ) 0 s := by
    intro s
    have h := (ray_deriv φ φ' hφ hφ'c θout hbout s).sub (ray_deriv φ φ' hφ hφ'c θin hbin s)
    rw [sub_self] at h
    exact h
  have hc := is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) p 0
  rw [hc, ofReal_zero]

/-- The Airy phase `φ_u(a) = exp(-u a + a³/3)`. -/
theorem phi_hasDerivAt (u : ℝ) (z : ℂ) :
    HasDerivAt (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3))
      (exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(u : ℂ) + z ^ 2)) z := by
  have h1 : HasDerivAt (fun a : ℂ => -(u : ℂ) * a + a ^ 3 / 3) (-(u : ℂ) * 1 + ((3 : ℕ) * z ^ (3 - 1)) / 3) z :=
    ((hasDerivAt_id' z).const_mul _).add ((hasDerivAt_pow 3 z).div_const 3)
  exact h1.cexp.congr_deriv (by norm_num)

theorem phi_ray_bound (u θ : ℝ) (hcos : Real.cos θ = 1 / 2) (hsin : Real.sin θ ^ 2 = 3 / 4) (R : ℝ) :
    ∃ B : ℝ, ∀ s : ℝ, |s| ≤ R → ∀ t : ℝ, 0 < t →
      ‖exp (-(u : ℂ) * ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) +
          ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3)‖ ≤ B * Real.exp (-t) ∧
      ‖exp (-(u : ℂ) * ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) +
          ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) *
        (-(u : ℂ) + ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 2)‖ ≤ B * Real.exp (-t) := by
  obtain ⟨D, hD⟩ := cubic_bound (|u| / 2 + R ^ 2 / 2 + 3) (R / 2)
  set K : ℝ := |u| * R + R ^ 3 / 3 + D with hK
  refine ⟨Real.exp K * (|u| + 2 * R ^ 2 + 9), fun s hs t ht => ?_⟩
  have hR0 : 0 ≤ R := (abs_nonneg s).trans hs
  set a : ℂ := (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hre, him⟩ := ray_point_re_im s t θ
  rw [← ha] at hre him
  rw [hcos] at hre
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hwre : (-(u : ℂ) * a + a ^ 3 / 3).re = -u * a.re + (a.re ^ 3 - 3 * a.re * a.im ^ 2) / 3 := by
    rw [Complex.add_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, ofReal_re, ofReal_im]
    ring
  have hexp : (-(u : ℂ) * a + a ^ 3 / 3).re ≤ K - 3 * t := by
    rw [hwre, him2, hre]
    have h1 : -u * s ≤ |u| * R := by
      have := neg_abs_le (u * s)
      rw [abs_mul] at this
      nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg u)]
    have h2 : s ^ 3 ≤ R ^ 3 :=
      ((Odd.strictMono_pow (by decide : Odd 3)).monotone (le_abs_self s)).trans
        (pow_le_pow_left₀ (abs_nonneg s) hs 3)
    have h3 : s ^ 2 * t ≤ R ^ 2 * t := by
      have : s ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs s]; exact pow_le_pow_left₀ (abs_nonneg s) hs 2
      exact mul_le_mul_of_nonneg_right this ht.le
    have h4 : -s * t ^ 2 ≤ R * t ^ 2 := by
      have : -s ≤ R := (neg_le_abs s).trans hs
      exact mul_le_mul_of_nonneg_right this (sq_nonneg t)
    have h5 : -u * t ≤ |u| * t := mul_le_mul_of_nonneg_right (neg_le_abs u) ht.le
    have h6 := hD t ht.le
    nlinarith
  have hE1 : Real.exp (-(u : ℂ) * a + a ^ 3 / 3).re ≤ Real.exp K * Real.exp (-3 * t) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have h31 : Real.exp (-3 * t) ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
  have hK0 : 0 < Real.exp K := Real.exp_pos K
  have hC : 1 ≤ |u| + 2 * R ^ 2 + 9 := by nlinarith [abs_nonneg u, sq_nonneg R]
  constructor
  · rw [norm_exp]
    calc Real.exp (-(u : ℂ) * a + a ^ 3 / 3).re ≤ Real.exp K * Real.exp (-3 * t) := hE1
      _ ≤ Real.exp K * Real.exp (-t) := mul_le_mul_of_nonneg_left h31 hK0.le
      _ ≤ Real.exp K * (|u| + 2 * R ^ 2 + 9) * Real.exp (-t) := by
        have := Real.exp_pos (-t)
        have h := mul_le_mul_of_nonneg_left hC (mul_pos hK0 this).le
        linarith [h]
  · have hna : ‖a‖ ≤ R + t := by
      rw [ha]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      linarith
    have hna2 : ‖a‖ ^ 2 ≤ 2 * R ^ 2 + 2 * t ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg a) hna 2
      nlinarith [sq_nonneg (R - t)]
    have ht2 : t ^ 2 ≤ 4 * Real.exp t := by
      have h := Real.add_one_le_exp (t / 2)
      have h' := pow_le_pow_left₀ (by linarith) h 2
      rw [← Real.exp_nat_mul] at h'
      have h'' : (t / 2 + 1) ^ 2 ≤ Real.exp t := by
        rwa [show ((2 : ℕ) : ℝ) * (t / 2) = t by push_cast; ring] at h'
      nlinarith
    have hP : ‖-(u : ℂ) + a ^ 2‖ ≤ |u| + 2 * R ^ 2 + 8 * Real.exp t := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      linarith
    rw [norm_mul, norm_exp]
    have hP0 : 0 ≤ ‖-(u : ℂ) + a ^ 2‖ := norm_nonneg _
    have e2 : Real.exp (-3 * t) * Real.exp t ≤ Real.exp (-t) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    calc Real.exp (-(u : ℂ) * a + a ^ 3 / 3).re * ‖-(u : ℂ) + a ^ 2‖
        ≤ (Real.exp K * Real.exp (-3 * t)) * (|u| + 2 * R ^ 2 + 8 * Real.exp t) :=
          mul_le_mul hE1 hP hP0 (by positivity)
      _ = Real.exp K * ((|u| + 2 * R ^ 2) * Real.exp (-3 * t) + 8 * (Real.exp (-3 * t) * Real.exp t)) := by
          ring
      _ ≤ Real.exp K * ((|u| + 2 * R ^ 2) * Real.exp (-t) + 8 * Real.exp (-t)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0.le
          have hu0 : 0 ≤ |u| + 2 * R ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h31 hu0]
      _ ≤ Real.exp K * (|u| + 2 * R ^ 2 + 9) * Real.exp (-t) := by
          have := Real.exp_pos (-t)
          nlinarith

theorem sin_pi_div_three_sq' : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

theorem cos_neg_pi_div_three : Real.cos (-Real.pi / 3) = 1 / 2 := by
  rw [neg_div, Real.cos_neg, Real.cos_pi_div_three]

theorem sin_neg_pi_div_three_sq : Real.sin (-Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [neg_div, Real.sin_neg, neg_sq, sin_pi_div_three_sq']

/-- Vertex independence for the Airy phase on the `±π/3` rays. -/
theorem airy_vertex (u p : ℝ) :
    rayIntegral (p : ℂ) (Real.pi / 3) (-Real.pi / 3) (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3)) =
      rayIntegral 0 (Real.pi / 3) (-Real.pi / 3) (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3)) :=
  rayIntegral_vertex_indep (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3))
    (fun z => exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(u : ℂ) + z ^ 2))
    (phi_hasDerivAt u) (by fun_prop) _ _
    (phi_ray_bound u _ Real.cos_pi_div_three sin_pi_div_three_sq')
    (phi_ray_bound u _ cos_neg_pi_div_three sin_neg_pi_div_three_sq) p

/-- At vertex `0` the Airy broken-line integral is purely imaginary. -/
theorem airy_re_zero (u : ℝ) :
    (rayIntegral 0 (Real.pi / 3) (-Real.pi / 3) (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3))).re = 0 := by
  unfold rayIntegral
  have he : exp (((-Real.pi / 3 : ℝ) : ℂ) * I) = (starRingEnd ℂ) (exp (((Real.pi / 3 : ℝ) : ℂ) * I)) := by
    rw [← exp_conj, map_mul, conj_ofReal, conj_I]; congr 1; push_cast; ring
  have hpt : ∀ t : ℝ,
      exp (-(u : ℂ) * (0 + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) +
        (0 + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) ^ 3 / 3) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) =
      (starRingEnd ℂ) (exp (-(u : ℂ) * (0 + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) +
        (0 + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) ^ 3 / 3) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) := by
    intro t
    have hφc : ∀ a : ℂ, exp (-(u : ℂ) * (starRingEnd ℂ) a + ((starRingEnd ℂ) a) ^ 3 / 3) =
        (starRingEnd ℂ) (exp (-(u : ℂ) * a + a ^ 3 / 3)) := by
      intro a
      have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := by apply Complex.ext <;> simp
      rw [← exp_conj]; congr 1; simp [h3]
    have h0 : (0 : ℂ) + (t : ℂ) * (starRingEnd ℂ) (exp (((Real.pi / 3 : ℝ) : ℂ) * I)) =
        (starRingEnd ℂ) (0 + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) := by simp
    rw [he, h0, hφc]
    exact (map_mul _ _ _).symm
  simp_rw [hpt]
  rw [integral_conj, Complex.sub_re, Complex.conj_re, sub_self]

theorem Ai_eq (u : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) * (I * rayIntegral 0 (Real.pi / 3) (-Real.pi / 3)
      (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3))) = (Ai u : ℂ) := by
  have h5 : exp (((5 * Real.pi / 6 : ℝ) : ℂ) * I) = I * exp (((Real.pi / 3 : ℝ) : ℂ) * I) := by
    rw [show (I : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) =
      exp ((Real.pi : ℂ) / 2 * I) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) by rw [exp_pi_div_two_mul_I],
      ← exp_add]
    congr 1; push_cast; ring
  have h1 : exp (((Real.pi / 6 : ℝ) : ℂ) * I) = I * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) := by
    rw [show (I : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) =
      exp ((Real.pi : ℂ) / 2 * I) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) by rw [exp_pi_div_two_mul_I],
      ← exp_add]
    congr 1; push_cast; ring
  have hrot : rayIntegral (I * 0) (5 * Real.pi / 6) (Real.pi / 6)
      (fun a => exp (I * (u : ℂ) * a + I * a ^ 3 / 3)) =
      I * rayIntegral 0 (Real.pi / 3) (-Real.pi / 3)
        (fun a => exp (I * (u : ℂ) * (I * a) + I * (I * a) ^ 3 / 3)) :=
    rayIntegral_rotate _ _ _ _ _ _ _ h5 h1
  have hfun : (fun a : ℂ => exp (I * (u : ℂ) * (I * a) + I * (I * a) ^ 3 / 3)) =
      fun a => exp (-(u : ℂ) * a + a ^ 3 / 3) := by
    funext a; congr 1; linear_combination ((u : ℂ) * a + (I ^ 2 - 1) * a ^ 3 / 3) * I_sq
  rw [hfun, mul_zero] at hrot
  have hAi : Ai u = ((1 / (2 * (Real.pi : ℂ))) * (I * rayIntegral 0 (Real.pi / 3) (-Real.pi / 3)
      (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3)))).re := by
    unfold Ai; rw [hrot]
  have hZim : ((1 / (2 * (Real.pi : ℂ))) * (I * rayIntegral 0 (Real.pi / 3) (-Real.pi / 3)
      (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3)))).im = 0 := by
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.im_ofReal_mul, I_mul_im, airy_re_zero, mul_zero]
  rw [hAi]
  exact Complex.ext (by simp) (by simp only [ofReal_im]; exact hZim)

theorem Hinf_zero (ε c u : ℝ) :
    Hinf ε 0 c u = ((Real.exp (-ε * u) / (2 * Real.pi) : ℝ) : ℂ) *
      rayIntegral 0 (Real.pi / 3) (-Real.pi / 3) (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3)) := by
  unfold Hinf
  rw [← airy_vertex u c]
  refine congrArg (fun F => _ * F) (congrArg (rayIntegral _ _ _) (funext fun a => ?_))
  simp

theorem Jinf_zero (ε c v : ℝ) :
    Jinf ε 0 c v = ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) *
      (-rayIntegral 0 (Real.pi / 3) (-Real.pi / 3) (fun a => exp (-(v : ℂ) * a + a ^ 3 / 3))) := by
  have hin : exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) = (-1) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) := by
    rw [show (-1 : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) =
      exp ((Real.pi : ℂ) * I) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) / exp (2 * (Real.pi : ℂ) * I) by
        rw [exp_pi_mul_I, exp_two_pi_mul_I]; ring, ← exp_add, ← exp_sub]
    congr 1; push_cast; ring
  have hout : exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) = (-1) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) := by
    rw [show (-1 : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) =
      exp ((Real.pi : ℂ) * I) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) by rw [exp_pi_mul_I], ← exp_add]
    congr 1; push_cast; ring
  have hrot : rayIntegral ((-1) * ((-c : ℝ) : ℂ)) (-2 * Real.pi / 3) (2 * Real.pi / 3)
      (fun a => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ 0) =
      (-1) * rayIntegral ((-c : ℝ) : ℂ) (Real.pi / 3) (-Real.pi / 3)
        (fun a => exp ((v : ℂ) * ((-1) * a) - ((-1) * a) ^ 3 / 3) * ((-1) * a) ^ 0) :=
    rayIntegral_rotate _ _ _ _ _ _ _ hin hout
  have hfun : (fun a : ℂ => exp ((v : ℂ) * ((-1) * a) - ((-1) * a) ^ 3 / 3) * ((-1) * a) ^ 0) =
      fun a => exp (-(v : ℂ) * a + a ^ 3 / 3) := by
    funext a; rw [pow_zero, mul_one]; congr 1; ring
  rw [hfun, show (-1 : ℂ) * ((-c : ℝ) : ℂ) = (c : ℂ) by push_cast; ring, airy_vertex v (-c)] at hrot
  unfold Jinf
  rw [hrot]
  ring

/-- `𝓗_∞ 𝓙_∞ = e^{-εu} Ai(u) Ai(v) e^{εv}` for `k = 0`, any real vertices. -/
theorem Hinf_Jinf_zero (ε cH cJ u v : ℝ) :
    Hinf ε 0 cH u * Jinf ε 0 cJ v =
      ((Real.exp (-ε * u) * Ai u * Ai v * Real.exp (ε * v) : ℝ) : ℂ) := by
  have hAu := Ai_eq u
  have hAv := Ai_eq v
  rw [Hinf_zero, Jinf_zero]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  set Xu := rayIntegral 0 (Real.pi / 3) (-Real.pi / 3) (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3))
  set Xv := rayIntegral 0 (Real.pi / 3) (-Real.pi / 3) (fun a => exp (-(v : ℂ) * a + a ^ 3 / 3))
  set E1 : ℂ := ((Real.exp (-ε * u) : ℝ) : ℂ)
  set E2 : ℂ := ((Real.exp (ε * v) : ℝ) : ℂ)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  linear_combination (-(E1 * E2 * (1 / (2 * (Real.pi : ℂ)) * Xu) * (1 / (2 * (Real.pi : ℂ)) * Xv))) * I_sq +
    (E1 * E2 * (Ai v : ℂ)) * hAu + (E1 * E2 * I * (1 / (2 * (Real.pi : ℂ)) * Xu)) * hAv

/-- eq_200 for `k = 0` (no vertex constraints needed). -/
theorem eq_200_zero (ε cH cJ u v : ℝ) :
    (∫ y in Ioi (0 : ℝ), Hinf ε 0 cH (u + y) * Jinf ε 0 cJ (v + y)) -
        (∫ y in Ioi (0 : ℝ),
          ((Real.exp (-ε * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (ε * (v + y)) : ℝ) : ℂ)) =
      ∑ m ∈ Finset.Icc 1 0,
        ((Real.exp (-ε * u) * sFn m u * tFn m v * Real.exp (ε * v) : ℝ) : ℂ) := by
  simp_rw [Hinf_Jinf_zero]
  simp

open SpikedWishart.SoftEdge in
theorem eq_200_k_zero_aux (ε cH cJ u v : ℝ) :
    (∫ y in Set.Ioi (0 : ℝ), Hinf ε 0 cH (u + y) * Jinf ε 0 cJ (v + y)) =
      ∫ y in Set.Ioi (0 : ℝ),
        ((Real.exp (-ε * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (ε * (v + y)) : ℝ) : ℂ) := by
  have h := eq_200_zero ε cH cJ u v
  rw [sub_eq_iff_eq_add] at h
  rw [h, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, zero_add]

end Lib5e

open SpikedWishart.SoftEdge MeasureTheory in
theorem solution (ε cH cJ u v : ℝ) :
    (∫ y in Set.Ioi (0 : ℝ), Hinf ε 0 cH (u + y) * Jinf ε 0 cJ (v + y)) =
      ∫ y in Set.Ioi (0 : ℝ),
        ((Real.exp (-ε * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (ε * (v + y)) : ℝ) : ℂ) := by
  exact Lib5e.eq_200_k_zero_aux ε cH cJ u v
