-- Prove2me | solution 1 for SpikedWishart.SoftEdge.eq_200
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T00:19:53.629009+00:00
-- url     : https://prove2.me/submissions/c88cf275-f1b8-4458-99ce-9fd0461dd61e

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace F506

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


/-- Norm bound for one ray integral from an exponentially decaying integrand bound. -/
theorem ray_integral_norm_le (φ : ℂ → ℂ) (c : ℂ) (θ B : ℝ)
    (h : ∀ t : ℝ, 0 < t → ‖φ (c + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t)) :
    ‖∫ t in Ioi (0 : ℝ), φ (c + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B := by
  have hg : Integrable (fun t : ℝ => B * Real.exp (-t)) (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) B
  have hb : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖φ (c + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B * Real.exp (-t) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    exact h t ht
  refine (norm_integral_le_of_norm_le hg hb).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, mul_one]

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
    nlinarith
  have hnorm2 : (-c / 2) ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre]
    nlinarith [sq_nonneg (t + c / 2), him2, sq_nonneg a.im]
  have hc2 : 0 < -c / 2 := by linarith
  have hnorm : -c / 2 ≤ ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (norm_nonneg a) hlt
    nlinarith
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

/-- Pointwise bound for the `𝓙_∞` integrand on a ray `c + t e^{iθ}` with `cos θ = -1/2`. -/
theorem J_integrand_bound (c x0 θ D : ℝ) (k : ℕ) (hc : c < 0) (hcos : Real.cos θ = -1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hD : ∀ t : ℝ, 0 ≤ t → (-x0 / 2 + c ^ 2 / 2 + 2) * t + (c / 2) * t ^ 2 - t ^ 3 / 3 ≤ D)
    (v : ℝ) (hv : x0 ≤ v) (t : ℝ) (ht : 0 < t) :
    ‖exp ((v : ℂ) * ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) -
        ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) *
        ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ k‖ ≤
      ((k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v)) * Real.exp (-t) := by
  set a : ℂ := (c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hre, him⟩ := ray_point_re_im c t θ
  rw [← ha] at hre him
  rw [hcos] at hre
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hwre : ((v : ℂ) * a - a ^ 3 / 3).re = v * a.re - (a.re ^ 3 - 3 * a.re * a.im ^ 2) / 3 := by
    rw [Complex.sub_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, ofReal_re, ofReal_im]
    ring
  have hexp : ((v : ℂ) * a - a ^ 3 / 3).re + (-c + t) ≤ (D - c ^ 3 / 3 - c) + c * v + -t := by
    rw [hwre, him2, hre]
    have h1 := hD t ht.le
    have h2 := mul_nonneg (sub_nonneg.2 hv) ht.le
    nlinarith
  have hna : ‖a‖ ≤ -c + t := by
    calc ‖a‖ ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * exp ((θ : ℂ) * I)‖ := norm_add_le _ _
      _ = -c + t := by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hc, abs_of_pos ht]
  have hx0 : 0 ≤ -c + t := by linarith
  have hfac : (-c + t) ^ k ≤ Real.exp (-c + t) * k.factorial := by
    have h := Real.pow_div_factorial_le_exp (x := -c + t) hx0 k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rwa [div_le_iff₀ hf] at h
  have hk : ‖a ^ k‖ ≤ Real.exp (-c + t) * k.factorial := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg a) hna k).trans hfac
  rw [norm_mul, norm_exp]
  calc Real.exp ((v : ℂ) * a - a ^ 3 / 3).re * ‖a ^ k‖
      ≤ Real.exp ((v : ℂ) * a - a ^ 3 / 3).re * (Real.exp (-c + t) * k.factorial) :=
        mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    _ = Real.exp (((v : ℂ) * a - a ^ 3 / 3).re + (-c + t)) * k.factorial := by
        rw [← mul_assoc, ← Real.exp_add]
    _ ≤ Real.exp ((D - c ^ 3 / 3 - c) + c * v + -t) * k.factorial :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hexp) (by positivity)
    _ = ((k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v)) * Real.exp (-t) := by
        rw [Real.exp_add, Real.exp_add]; ring


theorem sin_pi_div_three_sq : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

open SpikedWishart.SoftEdge in
/-- R7a. `|𝓗_∞(u)| ≤ C e^{-(ε+c)u}` on `[x₀, ∞)` for a vertex `c < 0`. -/
theorem Hinf_bound (ε : ℝ) (k : ℕ) (c x0 : ℝ) (hc : c < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, x0 ≤ u → ‖Hinf ε k c u‖ ≤ C * Real.exp (-(ε + c) * u) := by
  obtain ⟨D, hD⟩ := cubic_bound (-x0 / 2 + c ^ 2 / 2 + 1) (-c / 2)
  have h2c : 0 ≤ 2 / -c := div_nonneg (by norm_num) (by linarith)
  have hB0 : 0 ≤ (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) := by positivity
  refine ⟨(2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) / Real.pi, div_nonneg hB0 Real.pi_pos.le,
    fun u hu => ?_⟩
  have hcos1 : Real.cos (-Real.pi / 3) = 1 / 2 := by
    rw [neg_div, Real.cos_neg, Real.cos_pi_div_three]
  have hsin1 : Real.sin (-Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [neg_div, Real.sin_neg, neg_sq, sin_pi_div_three_sq]
  have hray : ∀ θ : ℝ, Real.cos θ = 1 / 2 → Real.sin θ ^ 2 = 3 / 4 →
      ‖∫ t in Ioi (0 : ℝ), (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k))
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤
        (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u) := by
    intro θ h1 h2
    refine ray_integral_norm_le (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k))
      (c : ℂ) θ _ (fun t ht => ?_)
    exact H_integrand_bound c x0 θ D k hc h1 h2 hD u hu t ht
  have hR : ‖rayIntegral (c : ℂ) (Real.pi / 3) (-Real.pi / 3)
      (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k))‖ ≤
        2 * ((2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u)) := by
    unfold rayIntegral
    refine (norm_sub_le _ _).trans ?_
    calc _ ≤ (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u) +
          (2 / -c) ^ k * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * u) :=
          add_le_add (hray (-Real.pi / 3) hcos1 hsin1)
            (hray (Real.pi / 3) Real.cos_pi_div_three sin_pi_div_three_sq)
      _ = _ := by ring
  unfold Hinf
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hR (by positivity)).trans (le_of_eq ?_)
  have he : Real.exp (-(ε + c) * u) = Real.exp (-ε * u) * Real.exp (-c * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  field_simp

open SpikedWishart.SoftEdge in
/-- R7b. `|𝓙_∞(v)| ≤ C e^{(ε+c)v}` on `[x₀, ∞)` for a vertex `c < 0`. -/
theorem Jinf_bound (ε : ℝ) (k : ℕ) (c x0 : ℝ) (hc : c < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, x0 ≤ v → ‖Jinf ε k c v‖ ≤ C * Real.exp ((ε + c) * v) := by
  obtain ⟨D, hD⟩ := cubic_bound (-x0 / 2 + c ^ 2 / 2 + 2) (c / 2)
  have hB0 : 0 ≤ (k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) := by positivity
  refine ⟨(k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) / Real.pi,
    div_nonneg hB0 Real.pi_pos.le, fun v hv => ?_⟩
  have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  have hcos1 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have hsin1 : Real.sin (2 * Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [h23, Real.sin_pi_sub, sin_pi_div_three_sq]
  have hm : -2 * Real.pi / 3 = -(2 * Real.pi / 3) := by ring
  have hcos2 : Real.cos (-2 * Real.pi / 3) = -1 / 2 := by rw [hm, Real.cos_neg, hcos1]
  have hsin2 : Real.sin (-2 * Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [hm, Real.sin_neg, neg_sq, hsin1]
  have hray : ∀ θ : ℝ, Real.cos θ = -1 / 2 → Real.sin θ ^ 2 = 3 / 4 →
      ‖∫ t in Ioi (0 : ℝ), (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k)
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤
        (k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v) := by
    intro θ h1 h2
    refine ray_integral_norm_le (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k)
      (c : ℂ) θ _ (fun t ht => ?_)
    exact J_integrand_bound c x0 θ D k hc h1 h2 hD v hv t ht
  have hR : ‖rayIntegral (c : ℂ) (-2 * Real.pi / 3) (2 * Real.pi / 3)
      (fun a => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k)‖ ≤
        2 * ((k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v)) := by
    unfold rayIntegral
    refine (norm_sub_le _ _).trans ?_
    calc _ ≤ (k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v) +
          (k.factorial : ℝ) * Real.exp (D - c ^ 3 / 3 - c) * Real.exp (c * v) :=
          add_le_add (hray (2 * Real.pi / 3) hcos1 hsin1) (hray (-2 * Real.pi / 3) hcos2 hsin2)
      _ = _ := by ring
  unfold Jinf
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hR (by positivity)).trans (le_of_eq ?_)
  have he : Real.exp ((ε + c) * v) = Real.exp (ε * v) * Real.exp (c * v) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  field_simp


/-! ## New for eq_200 (k ≥ 1): telescoping in `y`. -/

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

theorem sin_two_pi_div_three_sq : Real.sin (2 * Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, sin_pi_div_three_sq']

theorem cos_neg_two_pi_div_three : Real.cos (-2 * Real.pi / 3) = -1 / 2 := by
  rw [show -2 * Real.pi / 3 = -(2 * Real.pi / 3) by ring, Real.cos_neg, cos_two_pi_div_three]

theorem sin_neg_two_pi_div_three_sq : Real.sin (-2 * Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [show -2 * Real.pi / 3 = -(2 * Real.pi / 3) by ring, Real.sin_neg, neg_sq,
    sin_two_pi_div_three_sq]

theorem e56 : exp (((5 * Real.pi / 6 : ℝ) : ℂ) * I) = I * exp (((Real.pi / 3 : ℝ) : ℂ) * I) := by
  rw [show (I : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) =
    exp ((Real.pi : ℂ) / 2 * I) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) by rw [exp_pi_div_two_mul_I],
    ← exp_add]
  congr 1; push_cast; ring

theorem e16 : exp (((Real.pi / 6 : ℝ) : ℂ) * I) = I * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) := by
  rw [show (I : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) =
    exp ((Real.pi : ℂ) / 2 * I) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) by rw [exp_pi_div_two_mul_I],
    ← exp_add]
  congr 1; push_cast; ring

theorem em23 : exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) = (-1) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) := by
  rw [show (-1 : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) =
    exp ((Real.pi : ℂ) * I) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) / exp (2 * (Real.pi : ℂ) * I) by
      rw [exp_pi_mul_I, exp_two_pi_mul_I]; ring, ← exp_add, ← exp_sub]
  congr 1; push_cast; ring

theorem e23 : exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) = (-1) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) := by
  rw [show (-1 : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) =
    exp ((Real.pi : ℂ) * I) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) by rw [exp_pi_mul_I], ← exp_add]
  congr 1; push_cast; ring

theorem ray_ne_zero (s t θ : ℝ) (hs : s ≠ 0) (hθ : Real.sin θ ^ 2 = 3 / 4) :
    (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) ≠ 0 := by
  intro h
  obtain ⟨hre, him⟩ := ray_point_re_im s t θ
  rw [h, Complex.zero_im] at him
  rw [h, Complex.zero_re] at hre
  have hsin : Real.sin θ ≠ 0 := by
    intro h0; rw [h0] at hθ; norm_num at hθ
  have ht : t = 0 := by
    rcases mul_eq_zero.1 him.symm with h1 | h1
    · exact h1
    · exact absurd h1 hsin
  rw [ht] at hre
  apply hs
  linarith

theorem ray_norm_ge (s t θ : ℝ) (hcos : Real.cos θ = 1 / 2) (hsin : Real.sin θ ^ 2 = 3 / 4) :
    |s| / 2 ≤ ‖(s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)‖ := by
  set a : ℂ := (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hre, him⟩ := ray_point_re_im s t θ
  rw [← ha] at hre him
  rw [hcos] at hre
  have h2 : ‖a‖ ^ 2 = s ^ 2 + s * t + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    linear_combination t ^ 2 * hsin
  nlinarith [sq_abs s, sq_nonneg (t + s / 2), norm_nonneg a, abs_nonneg s]

theorem ray_inv_pow_le (s t θ : ℝ) (hs : s ≠ 0) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4) (m : ℕ) :
    ‖1 / ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ m‖ ≤ (2 / |s|) ^ m := by
  have hs' : 0 < |s| := abs_pos.2 hs
  have h1 := ray_norm_ge s t θ hcos hsin
  have h2 : 0 < |s| / 2 := by positivity
  rw [norm_div, norm_one, norm_pow, one_div, ← inv_pow]
  refine pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) ?_ m
  rw [← inv_div]
  exact inv_anti₀ h2 h1

theorem ray_pow_le (s t θ R : ℝ) (hs : |s| ≤ R) (ht : 0 < t) (n : ℕ) :
    ‖((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ n‖ ≤
      (n.factorial : ℝ) * Real.exp R * Real.exp t := by
  have hna : ‖(s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)‖ ≤ R + t := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    linarith
  rw [norm_pow]
  have h1 := Real.pow_div_factorial_le_exp (x := ‖(s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)‖)
    (norm_nonneg _) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h1
  calc _ ≤ Real.exp ‖(s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)‖ * n.factorial := h1
    _ ≤ Real.exp (R + t) * n.factorial :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hna) hf.le
    _ = _ := by rw [Real.exp_add]; ring

/-- Exponential bound for the `𝓙` phase on rays with `cos θ = -1/2`, uniform in the vertex. -/
theorem expJ_bound (v θ : ℝ) (hcos : Real.cos θ = -1 / 2) (hsin : Real.sin θ ^ 2 = 3 / 4) (R : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, |s| ≤ R → ∀ t : ℝ, 0 < t →
      ‖exp ((v : ℂ) * ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) -
          ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3)‖ ≤ K * Real.exp (-3 * t) := by
  obtain ⟨D, hD⟩ := cubic_bound (|v| / 2 + R ^ 2 / 2 + 3) (R / 2)
  set K : ℝ := |v| * R + R ^ 3 / 3 + D with hK
  refine ⟨Real.exp K, Real.exp_pos K, fun s hs t ht => ?_⟩
  set a : ℂ := (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hre, him⟩ := ray_point_re_im s t θ
  rw [← ha] at hre him
  rw [hcos] at hre
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hwre : ((v : ℂ) * a - a ^ 3 / 3).re = v * a.re - (a.re ^ 3 - 3 * a.re * a.im ^ 2) / 3 := by
    rw [Complex.sub_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, ofReal_re, ofReal_im]
    ring
  have hexp : ((v : ℂ) * a - a ^ 3 / 3).re ≤ K - 3 * t := by
    rw [hwre, him2, hre]
    have h1 : v * s ≤ |v| * R := by
      have := le_abs_self (v * s)
      rw [abs_mul] at this
      nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg v), abs_nonneg s]
    have h2 : -s ^ 3 ≤ R ^ 3 := by
      have : (-s) ^ 3 ≤ R ^ 3 :=
        ((Odd.strictMono_pow (by decide : Odd 3)).monotone (neg_le_abs s)).trans
          (pow_le_pow_left₀ (abs_nonneg s) hs 3)
      nlinarith [this]
    have h3 : s ^ 2 * t ≤ R ^ 2 * t := by
      have : s ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs s]; exact pow_le_pow_left₀ (abs_nonneg s) hs 2
      exact mul_le_mul_of_nonneg_right this ht.le
    have h4 : s * t ^ 2 ≤ R * t ^ 2 := by
      have : s ≤ R := (le_abs_self s).trans hs
      exact mul_le_mul_of_nonneg_right this (sq_nonneg t)
    have h5 : -v * t ≤ |v| * t := mul_le_mul_of_nonneg_right (neg_le_abs v) ht.le
    have h6 := hD t ht.le
    nlinarith
  rw [norm_exp, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

theorem exp_poly_le {x y K Q t : ℝ} (hK : 0 ≤ K) (hy : 0 ≤ y)
    (h1 : x ≤ K * Real.exp (-3 * t)) (h2 : y ≤ Q * Real.exp t) (ht : 0 < t) :
    x * y ≤ K * Q * Real.exp (-t) := by
  have hQ : 0 ≤ Q := (mul_nonneg_iff_of_pos_right (Real.exp_pos t)).1 (hy.trans h2)
  have he : Real.exp (-3 * t) * Real.exp t = Real.exp (-2 * t) := by
    rw [← Real.exp_add]; ring_nf
  calc x * y ≤ (K * Real.exp (-3 * t)) * (Q * Real.exp t) :=
        mul_le_mul h1 h2 hy (by positivity)
    _ = K * Q * (Real.exp (-3 * t) * Real.exp t) := by ring
    _ = K * Q * Real.exp (-2 * t) := by rw [he]
    _ ≤ K * Q * Real.exp (-t) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (mul_nonneg hK hQ)

/-! ### Vertex shift for integrands holomorphic off `0` (negative real vertices). -/

theorem ray_deriv_neg (φ φ' : ℂ → ℂ) (hφ : ∀ z, z ≠ 0 → HasDerivAt φ (φ' z) z)
    (hφ'c : ContinuousOn φ' {0}ᶜ) (θ : ℝ) (hsin : Real.sin θ ^ 2 = 3 / 4) (s0 : ℝ) (hs0 : s0 < 0)
    (hb : ∃ B : ℝ, ∀ s : ℝ, |s - s0| < -s0 / 2 → ∀ t : ℝ, 0 < t →
      ‖φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t)) :
    HasDerivAt (fun s : ℝ => ∫ t in Ioi (0 : ℝ),
      φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) (-φ s0) s0 := by
  obtain ⟨B, hB⟩ := hb
  have hω : ‖exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  have hline : ∀ s : ℝ, Continuous fun t : ℝ => (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) :=
    fun s => continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hne : ∀ s : ℝ, s < 0 → ∀ t : ℝ, (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) ≠ 0 :=
    fun s hs t => ray_ne_zero s t θ hs.ne hsin
  have hδ : 0 < -s0 / 2 := by linarith
  have hball : ∀ s ∈ Metric.ball s0 (-s0 / 2), s < 0 := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have := (abs_lt.1 hs).2
    linarith
  have hcomp : ∀ s : ℝ, s < 0 →
      Continuous fun t : ℝ => φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) :=
    fun s hs => continuous_iff_continuousAt.2 fun t =>
      (hφ _ (hne s hs t)).continuousAt.comp
        (f := fun t : ℝ => (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) (hline s).continuousAt
  have hcomp' : Continuous fun t : ℝ => φ' ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) :=
    hφ'c.comp_continuous (hline s0) (fun t => Set.mem_compl_singleton_iff.2 (hne s0 hs0 t))
  have hbi : Integrable (fun t : ℝ => B * Real.exp (-t)) (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) B
  have h00 : |s0 - s0| < -s0 / 2 := by rw [sub_self, abs_zero]; exact hδ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℝ) (t : ℝ) => φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
    (F' := fun (s : ℝ) (t : ℝ) => φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
    (x₀ := s0) (bound := fun t => B * Real.exp (-t)) (s := Metric.ball s0 (-s0 / 2))
    (Metric.ball_mem_nhds s0 hδ)
    (Filter.eventually_of_mem (Iio_mem_nhds hs0) fun s hs =>
      ((hcomp s hs).mul continuous_const).aestronglyMeasurable)
    (by
      refine hbi.mono' ((hcomp s0 hs0).mul continuous_const).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [norm_mul, hω, mul_one]
      exact (hB s0 h00 t ht).1)
    ((hcomp'.mul continuous_const).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht s hs => ?_)
      have hs' : |s - s0| < -s0 / 2 := by
        rw [Metric.mem_ball, Real.dist_eq] at hs; exact hs
      show ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B * Real.exp (-t)
      rw [norm_mul, hω, mul_one]
      exact (hB s hs' t ht).2)
    hbi
    (by
      refine Filter.Eventually.of_forall (fun t s hs => ?_)
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) 1 s :=
        ((hasDerivAt_id' (s : ℂ)).comp_ofReal).add_const _
      have h2 := ((hφ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) (hne s (hball s hs) t)).comp s
        h1).mul_const (exp ((θ : ℂ) * I))
      rw [mul_one] at h2
      exact h2)
  have hval : ∫ t in Ioi (0 : ℝ), φ' ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I) =
      -φ s0 := by
    have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => φ ((s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I)))
        (φ' ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) t := by
      intro t _
      have h1 : HasDerivAt (fun y : ℝ => (s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I))
          (exp ((θ : ℂ) * I)) t := by
        have := (((hasDerivAt_id' (t : ℂ)).comp_ofReal).mul_const (exp ((θ : ℂ) * I))).const_add
          (s0 : ℂ)
        rw [one_mul] at this
        exact this
      exact (hφ _ (hne s0 hs0 t)).comp t h1
    have hlim : Tendsto (fun y : ℝ => φ ((s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hE : Tendsto (fun y : ℝ => B * Real.exp (-y)) atTop (𝓝 0) := by
        simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul B)
      refine squeeze_zero' (Filter.Eventually.of_forall (fun y => norm_nonneg _)) ?_ hE
      filter_upwards [Filter.eventually_gt_atTop 0] with y hy
      exact (hB s0 h00 y hy).1
    have := integral_Ioi_of_hasDerivAt_of_tendsto
      ((hcomp s0 hs0).continuousWithinAt) hd key.1 hlim
    rw [this]
    simp
  rw [← hval]
  exact key.2

theorem rayIntegral_vertex_neg (φ φ' : ℂ → ℂ) (hφ : ∀ z, z ≠ 0 → HasDerivAt φ (φ' z) z)
    (hφ'c : ContinuousOn φ' {0}ᶜ) (θin θout : ℝ) (hsin_in : Real.sin θin ^ 2 = 3 / 4)
    (hsin_out : Real.sin θout ^ 2 = 3 / 4)
    (hbin : ∀ s0 : ℝ, s0 < 0 → ∃ B : ℝ, ∀ s : ℝ, |s - s0| < -s0 / 2 → ∀ t : ℝ, 0 < t →
      ‖φ ((s : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I))‖ ≤ B * Real.exp (-t))
    (hbout : ∀ s0 : ℝ, s0 < 0 → ∃ B : ℝ, ∀ s : ℝ, |s - s0| < -s0 / 2 → ∀ t : ℝ, 0 < t →
      ‖φ ((s : ℂ) + (t : ℂ) * exp ((θout : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θout : ℂ) * I))‖ ≤ B * Real.exp (-t))
    (p p' : ℝ) (hp : p < 0) (hp' : p' < 0) :
    rayIntegral (p : ℂ) θin θout φ = rayIntegral (p' : ℂ) θin θout φ := by
  have hD : ∀ s ∈ Iio (0 : ℝ), HasDerivAt (fun s : ℝ => rayIntegral (s : ℂ) θin θout φ) 0 s := by
    intro s hs
    have h := (ray_deriv_neg φ φ' hφ hφ'c θout hsin_out s hs (hbout s hs)).sub
      (ray_deriv_neg φ φ' hφ hφ'c θin hsin_in s hs (hbin s hs))
    rw [sub_self] at h
    exact h
  exact isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
    (fun s hs => (hD s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hD s hs).deriv) (x := p) (y := p') hp hp'

end F506

namespace F506

open MeasureTheory Filter Topology Set Complex
open SpikedWishart.SoftEdge

noncomputable def HH (c : ℝ) (m : ℕ) (u : ℝ) : ℂ :=
  rayIntegral (c : ℂ) (Real.pi / 3) (-Real.pi / 3) (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ m))

noncomputable def JJ (c : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  rayIntegral (c : ℂ) (-2 * Real.pi / 3) (2 * Real.pi / 3) (fun a => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n)

theorem Hinf_HH (ε : ℝ) (k : ℕ) (c u : ℝ) :
    Hinf ε k c u = ((Real.exp (-ε * u) / (2 * Real.pi) : ℝ) : ℂ) * HH c k u := rfl

theorem Jinf_JJ (ε : ℝ) (k : ℕ) (c v : ℝ) :
    Jinf ε k c v = ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) * JJ c k v := rfl

theorem rayIntegral_const_mul (c : ℂ) (θin θout : ℝ) (κ : ℂ) (φ : ℂ → ℂ) :
    rayIntegral c θin θout (fun a => κ * φ a) = κ * rayIntegral c θin θout φ := by
  unfold rayIntegral
  rw [mul_sub, ← integral_const_mul, ← integral_const_mul]
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall fun t => by dsimp only; ring)
  · exact integral_congr_ae (Filter.Eventually.of_forall fun t => by dsimp only; ring)

/-! ### `𝓗` family: vertex shift between negative vertices. -/

theorem phiH_hasDerivAt (u : ℝ) (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ m))
      (exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(u : ℂ) + z ^ 2) * (1 / z ^ m) +
        exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(m : ℂ) * (1 / z ^ m) * (1 / z))) z := by
  have hinv : HasDerivAt (fun a : ℂ => 1 / a ^ m) (-(m : ℂ) * (1 / z ^ m) * (1 / z)) z := by
    have h := (hasDerivAt_pow m z).inv (pow_ne_zero m hz)
    have hf : (fun a : ℂ => 1 / a ^ m) = fun a => (a ^ m)⁻¹ := by
      funext a; rw [one_div]
    rw [hf]
    refine h.congr_deriv ?_
    cases m with
    | zero => simp
    | succ n =>
      rw [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  exact (phi_hasDerivAt u z).mul hinv

theorem phiH_bound (u θ : ℝ) (hcos : Real.cos θ = 1 / 2) (hsin : Real.sin θ ^ 2 = 3 / 4) (m : ℕ)
    (s0 : ℝ) (hs0 : s0 < 0) :
    ∃ B : ℝ, ∀ s : ℝ, |s - s0| < -s0 / 2 → ∀ t : ℝ, 0 < t →
      ‖(fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ m))
          ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖(fun z : ℂ => exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(u : ℂ) + z ^ 2) * (1 / z ^ m) +
          exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(m : ℂ) * (1 / z ^ m) * (1 / z)))
          ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) := by
  obtain ⟨B0, hB0⟩ := phi_ray_bound u θ hcos hsin (-2 * s0)
  have hL0 : 0 ≤ 4 / (-s0) := div_nonneg (by norm_num) (by linarith)
  refine ⟨|B0| * (4 / (-s0)) ^ m * (1 + m * (4 / (-s0))), fun s hs t ht => ?_⟩
  have hs1 := abs_lt.1 hs
  have hsneg : s < 0 := by linarith [hs1.2]
  have hsR : |s| ≤ -2 * s0 := by rw [abs_of_neg hsneg]; linarith [hs1.1]
  have hsabs : -s0 / 2 ≤ |s| := by rw [abs_of_neg hsneg]; linarith [hs1.2]
  have h2L : 2 / |s| ≤ 4 / (-s0) := by
    rw [div_le_div_iff₀ (abs_pos.2 hsneg.ne) (by linarith)]; linarith
  have h2L0 : 0 ≤ 2 / |s| := by positivity
  obtain ⟨h1, h2⟩ := hB0 s hsR t ht
  have hY : ‖1 / ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ m‖ ≤ (4 / (-s0)) ^ m :=
    (ray_inv_pow_le s t θ hsneg.ne hcos hsin m).trans (pow_le_pow_left₀ h2L0 h2L m)
  have hW : ‖1 / ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ 4 / (-s0) := by
    have := ray_inv_pow_le s t θ hsneg.ne hcos hsin 1
    rw [pow_one, pow_one] at this
    exact this.trans h2L
  have hE := Real.exp_pos (-t)
  have h1' := h1.trans (mul_le_mul_of_nonneg_right (le_abs_self B0) hE.le)
  have h2' := h2.trans (mul_le_mul_of_nonneg_right (le_abs_self B0) hE.le)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hLm : 0 ≤ (4 / (-s0)) ^ m := pow_nonneg hL0 m
  have hBLe : 0 ≤ |B0| * (4 / (-s0)) ^ m * Real.exp (-t) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hLm) hE.le
  have h1mL : 1 ≤ 1 + (m : ℝ) * (4 / (-s0)) := le_add_of_nonneg_right (mul_nonneg hm0 hL0)
  constructor
  · refine (norm_mul_le _ _).trans ?_
    calc _ ≤ (|B0| * Real.exp (-t)) * (4 / (-s0)) ^ m :=
          mul_le_mul h1' hY (norm_nonneg _) (by positivity)
      _ = (|B0| * (4 / (-s0)) ^ m * Real.exp (-t)) * 1 := by ring
      _ ≤ (|B0| * (4 / (-s0)) ^ m * Real.exp (-t)) * (1 + m * (4 / (-s0))) :=
          mul_le_mul_of_nonneg_left h1mL hBLe
      _ = _ := by ring
  · refine (norm_add_le _ _).trans ?_
    have hNYW : ‖-(m : ℂ) * (1 / ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ m) *
        (1 / ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)))‖ ≤ (m : ℝ) * (4 / (-s0)) ^ m * (4 / (-s0)) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_natCast]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hY hm0) hW (norm_nonneg _) (mul_nonneg hm0 hLm)
    have hA := (norm_mul_le _ _).trans (mul_le_mul h2' hY (norm_nonneg _) (by positivity))
    have hB := (norm_mul_le _ _).trans (mul_le_mul h1' hNYW (norm_nonneg _) (by positivity))
    calc _ ≤ |B0| * Real.exp (-t) * (4 / (-s0)) ^ m +
          |B0| * Real.exp (-t) * ((m : ℝ) * (4 / (-s0)) ^ m * (4 / (-s0))) := add_le_add hA hB
      _ = _ := by ring

theorem HH_vertex (m : ℕ) (u p p' : ℝ) (hp : p < 0) (hp' : p' < 0) : HH p m u = HH p' m u := by
  have hc : ContinuousOn (fun z : ℂ => exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(u : ℂ) + z ^ 2) * (1 / z ^ m) +
        exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(m : ℂ) * (1 / z ^ m) * (1 / z))) {0}ᶜ := by
    have hpow : ContinuousOn (fun z : ℂ => 1 / z ^ m) {0}ᶜ :=
      continuousOn_const.div (continuous_pow m).continuousOn
        (fun z hz => pow_ne_zero m (Set.mem_compl_singleton_iff.1 hz))
    have hinv : ContinuousOn (fun z : ℂ => 1 / z) {0}ᶜ :=
      continuousOn_const.div continuousOn_id (fun z hz => Set.mem_compl_singleton_iff.1 hz)
    have hE : Continuous (fun z : ℂ => exp (-(u : ℂ) * z + z ^ 3 / 3)) := by fun_prop
    have hP : Continuous (fun z : ℂ => -(u : ℂ) + z ^ 2) := by fun_prop
    exact ((hE.continuousOn.mul hP.continuousOn).mul hpow).add
      (hE.continuousOn.mul ((continuousOn_const.mul hpow).mul hinv))
  exact rayIntegral_vertex_neg _ _ (phiH_hasDerivAt u m) hc _ _ sin_pi_div_three_sq'
    sin_neg_pi_div_three_sq
    (fun s0 hs0 => phiH_bound u _ Real.cos_pi_div_three sin_pi_div_three_sq' m s0 hs0)
    (fun s0 hs0 => phiH_bound u _ cos_neg_pi_div_three sin_neg_pi_div_three_sq m s0 hs0) p p' hp hp'

/-! ### `𝓙` family: vertex independence (entire integrand). -/

theorem phiJ_hasDerivAt (v : ℝ) (n : ℕ) (z : ℂ) :
    HasDerivAt (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n)
      (exp ((v : ℂ) * z - z ^ 3 / 3) * ((v : ℂ) * z ^ n - z ^ (n + 2) + (n : ℂ) * z ^ (n - 1))) z := by
  have h1 : HasDerivAt (fun a : ℂ => (v : ℂ) * a - a ^ 3 / 3)
      ((v : ℂ) * 1 - ((3 : ℕ) * z ^ (3 - 1)) / 3) z :=
    ((hasDerivAt_id' z).const_mul _).sub ((hasDerivAt_pow 3 z).div_const 3)
  have h1' : HasDerivAt (fun a : ℂ => (v : ℂ) * a - a ^ 3 / 3) ((v : ℂ) - z ^ 2) z :=
    h1.congr_deriv (by norm_num)
  exact (h1'.cexp.mul (hasDerivAt_pow n z)).congr_deriv (by ring)

theorem phiJ_bound (v θ : ℝ) (hcos : Real.cos θ = -1 / 2) (hsin : Real.sin θ ^ 2 = 3 / 4) (n : ℕ)
    (R : ℝ) :
    ∃ B : ℝ, ∀ s : ℝ, |s| ≤ R → ∀ t : ℝ, 0 < t →
      ‖(fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n)
          ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖(fun z : ℂ => exp ((v : ℂ) * z - z ^ 3 / 3) *
          ((v : ℂ) * z ^ n - z ^ (n + 2) + (n : ℂ) * z ^ (n - 1)))
          ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) := by
  obtain ⟨K, hK, hKb⟩ := expJ_bound v θ hcos hsin R
  refine ⟨K * (((n.factorial : ℝ) + |v| * n.factorial + (n + 2).factorial +
    n * (n - 1).factorial) * Real.exp R), fun s hs t ht => ?_⟩
  have hE := hKb s hs t ht
  have p0 := ray_pow_le s t θ R hs ht n
  have p2 := ray_pow_le s t θ R hs ht (n + 2)
  have p1 := ray_pow_le s t θ R hs ht (n - 1)
  have hf0 : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have heR := Real.exp_pos R
  have het := Real.exp_pos t
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hextra : 0 ≤ (|v| * (n.factorial : ℝ) + ((n + 2).factorial : ℝ) + n * ((n - 1).factorial : ℝ)) *
      (Real.exp R * Real.exp t) := by positivity
  constructor
  · refine (norm_mul_le _ _).trans (exp_poly_le hK.le (norm_nonneg _) hE (p0.trans ?_) ht)
    nlinarith
  · refine (norm_mul_le _ _).trans (exp_poly_le hK.le (norm_nonneg _) hE ?_ ht)
    have hP : ‖(v : ℂ) * ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ n -
        ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ (n + 2) +
        (n : ℂ) * ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ (n - 1)‖ ≤
        |v| * ‖((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ n‖ +
          ‖((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ (n + 2)‖ +
          n * ‖((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ (n - 1)‖ := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      · rw [norm_mul, Complex.norm_natCast]
    refine hP.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left p0 (abs_nonneg v), mul_le_mul_of_nonneg_left p1 hn0, p2,
      mul_nonneg hf0 (mul_nonneg heR.le het.le)]

theorem JJ_vertex (n : ℕ) (v p : ℝ) : JJ p n v = JJ 0 n v := by
  have h := rayIntegral_vertex_indep (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n)
    (fun z => exp ((v : ℂ) * z - z ^ 3 / 3) * ((v : ℂ) * z ^ n - z ^ (n + 2) + (n : ℂ) * z ^ (n - 1)))
    (phiJ_hasDerivAt v n) (by fun_prop) (-2 * Real.pi / 3) (2 * Real.pi / 3)
    (phiJ_bound v _ cos_neg_two_pi_div_three sin_neg_two_pi_div_three_sq n)
    (phiJ_bound v _ cos_two_pi_div_three sin_two_pi_div_three_sq n) p
  unfold JJ
  rw [h, Complex.ofReal_zero]

/-! ### Parametric derivatives. -/

theorem ray_param_deriv (Φ Φ' : ℝ → ℂ → ℂ) (c θ u0 B : ℝ)
    (hd : ∀ u : ℝ, ∀ t : ℝ, 0 < t →
      HasDerivAt (fun u => Φ u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)))
        (Φ' u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))) u)
    (hm : ∀ u : ℝ, Continuous fun t : ℝ => Φ u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)))
    (hm' : Continuous fun t : ℝ => Φ' u0 ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)))
    (hb : ∀ u : ℝ, |u - u0| < 1 → ∀ t : ℝ, 0 < t →
      ‖Φ u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖Φ' u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t)) :
    HasDerivAt (fun u : ℝ => ∫ t in Ioi (0 : ℝ),
        Φ u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
      (∫ t in Ioi (0 : ℝ), Φ' u0 ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) u0 := by
  have hω : ‖exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  have hbi : Integrable (fun t : ℝ => B * Real.exp (-t)) (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) B
  have h00 : |u0 - u0| < 1 := by rw [sub_self, abs_zero]; exact one_pos
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (u : ℝ) (t : ℝ) => Φ u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
    (F' := fun (u : ℝ) (t : ℝ) => Φ' u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
    (x₀ := u0) (bound := fun t => B * Real.exp (-t)) (s := Metric.ball u0 1)
    (Metric.ball_mem_nhds u0 one_pos)
    (Filter.Eventually.of_forall fun u => ((hm u).mul continuous_const).aestronglyMeasurable)
    (by
      refine hbi.mono' ((hm u0).mul continuous_const).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [norm_mul, hω, mul_one]
      exact (hb u0 h00 t ht).1)
    ((hm'.mul continuous_const).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht u hu => ?_)
      rw [Metric.mem_ball, Real.dist_eq] at hu
      show ‖Φ' u ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B * Real.exp (-t)
      rw [norm_mul, hω, mul_one]
      exact (hb u hu t ht).2)
    hbi
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht u _ => ?_)
      exact (hd u t ht).mul_const _)
  exact key.2

theorem hasDerivAt_phiH_u (m : ℕ) (a : ℂ) (ha : a ≠ 0) (u : ℝ) :
    HasDerivAt (fun u : ℝ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ (m + 1)))
      (-(exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ m))) u := by
  have h1 : HasDerivAt (fun u : ℝ => -(u : ℂ) * a + a ^ 3 / 3) (-a) u := by
    have := (((hasDerivAt_id' (u : ℂ)).comp_ofReal).neg.mul_const a).add_const (a ^ 3 / 3)
    exact this.congr_deriv (by ring)
  refine (h1.cexp.mul_const (1 / a ^ (m + 1))).congr_deriv ?_
  field_simp <;> ring

theorem hasDerivAt_phiJ_v (n : ℕ) (a : ℂ) (v : ℝ) :
    HasDerivAt (fun v : ℝ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n)
      (exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ (n + 1)) v := by
  have h1 : HasDerivAt (fun v : ℝ => (v : ℂ) * a - a ^ 3 / 3) a v := by
    have := (((hasDerivAt_id' (v : ℂ)).comp_ofReal).mul_const a).sub_const (a ^ 3 / 3)
    exact this.congr_deriv (by ring)
  exact (h1.cexp.mul_const (a ^ n)).congr_deriv (by ring)

theorem HH_hasDerivAt (c : ℝ) (m : ℕ) (hc : c < 0) (u0 : ℝ) :
    HasDerivAt (fun u => HH c (m + 1) u) (-HH c m u0) u0 := by
  obtain ⟨D, hD⟩ := cubic_bound (-(u0 - 1) / 2 + c ^ 2 / 2 + 1) (-c / 2)
  have h2c : 0 ≤ 2 / -c := div_nonneg (by norm_num) (by linarith)
  have hray : ∀ θ : ℝ, Real.cos θ = 1 / 2 → Real.sin θ ^ 2 = 3 / 4 →
      HasDerivAt (fun u : ℝ => ∫ t in Ioi (0 : ℝ),
          (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ (m + 1)))
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
        (-∫ t in Ioi (0 : ℝ), (fun a : ℂ => exp (-(u0 : ℂ) * a + a ^ 3 / 3) * (1 / a ^ m))
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) u0 := by
    intro θ hcos hsin
    have hne : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) ≠ 0 :=
      fun t => ray_ne_zero c t θ hc.ne hsin
    have hline : Continuous fun t : ℝ => (c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcontk : ∀ (k : ℕ) (u : ℝ), Continuous fun t : ℝ =>
        exp (-(u : ℂ) * ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) +
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) *
          (1 / ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ k) := by
      intro k u
      exact Continuous.mul (by fun_prop)
        (continuous_const.div (hline.pow k) (fun t => pow_ne_zero k (hne t)))
    have hp1 : 0 ≤ (2 / -c) ^ (m + 1) := pow_nonneg h2c _
    have hp0 : 0 ≤ (2 / -c) ^ m := pow_nonneg h2c _
    have hA : 0 ≤ Real.exp (D + c ^ 3 / 3) := (Real.exp_pos _).le
    have h := ray_param_deriv (fun u a => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ (m + 1)))
      (fun u a => -(exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ m))) c θ u0
      (((2 / -c) ^ (m + 1) + (2 / -c) ^ m) * Real.exp (D + c ^ 3 / 3) * Real.exp (-c * (u0 + 1)))
      (fun u t _ => hasDerivAt_phiH_u m _ (hne t) u)
      (fun u => hcontk (m + 1) u) ((hcontk m u0).neg)
      (by
        intro u hu t ht
        have hu' := abs_lt.1 hu
        have hx : u0 - 1 ≤ u := by linarith [hu'.1]
        have heu : Real.exp (-c * u) ≤ Real.exp (-c * (u0 + 1)) :=
          Real.exp_le_exp.2 (by nlinarith [hu'.2])
        have b1 := H_integrand_bound c (u0 - 1) θ D (m + 1) hc hcos hsin hD u hx t ht
        have b0 := H_integrand_bound c (u0 - 1) θ D m hc hcos hsin hD u hx t ht
        have hEt := Real.exp_pos (-t)
        constructor
        · refine b1.trans (mul_le_mul_of_nonneg_right ?_ hEt.le)
          exact mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hp0) hA) heu
            (Real.exp_pos _).le (mul_nonneg (add_nonneg hp1 hp0) hA)
        · show ‖-(exp (-(u : ℂ) * ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) +
              ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) *
              (1 / ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ m))‖ ≤ _
          rw [norm_neg]
          refine b0.trans (mul_le_mul_of_nonneg_right ?_ hEt.le)
          exact mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hp1) hA) heu
            (Real.exp_pos _).le (mul_nonneg (add_nonneg hp1 hp0) hA))
    refine h.congr_deriv ?_
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    ring
  unfold HH rayIntegral
  have := (hray (-Real.pi / 3) cos_neg_pi_div_three sin_neg_pi_div_three_sq).sub
    (hray (Real.pi / 3) Real.cos_pi_div_three sin_pi_div_three_sq')
  refine this.congr_deriv ?_
  ring

theorem JJ_hasDerivAt (c : ℝ) (n : ℕ) (hc : c < 0) (v0 : ℝ) :
    HasDerivAt (fun v => JJ c n v) (JJ c (n + 1) v0) v0 := by
  obtain ⟨D, hD⟩ := cubic_bound (-(v0 - 1) / 2 + c ^ 2 / 2 + 2) (c / 2)
  have hray : ∀ θ : ℝ, Real.cos θ = -1 / 2 → Real.sin θ ^ 2 = 3 / 4 →
      HasDerivAt (fun v : ℝ => ∫ t in Ioi (0 : ℝ),
          (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n)
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
        (∫ t in Ioi (0 : ℝ), (fun a : ℂ => exp ((v0 : ℂ) * a - a ^ 3 / 3) * a ^ (n + 1))
          ((c : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) v0 := by
    intro θ hcos hsin
    have hA : 0 ≤ Real.exp (D - c ^ 3 / 3 - c) := (Real.exp_pos _).le
    have hf0 : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
    have hf1 : (0 : ℝ) ≤ (n + 1).factorial := Nat.cast_nonneg _
    exact ray_param_deriv (fun v a => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n)
      (fun v a => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ (n + 1)) c θ v0
      ((((n.factorial : ℝ) + (n + 1).factorial) * Real.exp (D - c ^ 3 / 3 - c)) *
        Real.exp (c * (v0 - 1)))
      (fun v t _ => hasDerivAt_phiJ_v n _ v)
      (fun v => by fun_prop) (by fun_prop)
      (by
        intro v hv t ht
        have hv' := abs_lt.1 hv
        have hx : v0 - 1 ≤ v := by linarith [hv'.1]
        have hev : Real.exp (c * v) ≤ Real.exp (c * (v0 - 1)) :=
          Real.exp_le_exp.2 (by nlinarith [hv'.1])
        have b0 := J_integrand_bound c (v0 - 1) θ D n hc hcos hsin hD v hx t ht
        have b1 := J_integrand_bound c (v0 - 1) θ D (n + 1) hc hcos hsin hD v hx t ht
        have hEt := Real.exp_pos (-t)
        constructor
        · refine b0.trans (mul_le_mul_of_nonneg_right ?_ hEt.le)
          exact mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hf1) hA) hev
            (Real.exp_pos _).le (mul_nonneg (add_nonneg hf0 hf1) hA)
        · refine b1.trans (mul_le_mul_of_nonneg_right ?_ hEt.le)
          exact mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hf0) hA) hev
            (Real.exp_pos _).le (mul_nonneg (add_nonneg hf0 hf1) hA))
  unfold JJ rayIntegral
  exact (hray (2 * Real.pi / 3) cos_two_pi_div_three sin_two_pi_div_three_sq).sub
    (hray (-2 * Real.pi / 3) cos_neg_two_pi_div_three sin_neg_two_pi_div_three_sq)

theorem HH_measurable (c : ℝ) (m : ℕ) (hc : c < 0) : Measurable (HH c m) := by
  have h : HH c m = fun w => -deriv (fun u => HH c (m + 1) u) w := by
    funext w; rw [(HH_hasDerivAt c m hc w).deriv, neg_neg]
  rw [h]
  exact (measurable_deriv _).neg

theorem JJ_continuous (c : ℝ) (n : ℕ) (hc : c < 0) : Continuous (JJ c n) :=
  continuous_iff_continuousAt.2 fun v => (JJ_hasDerivAt c n hc v).continuousAt

theorem HH_bound (c : ℝ) (m : ℕ) (x0 : ℝ) (hc : c < 0) :
    ∃ C : ℝ, ∀ u : ℝ, x0 ≤ u → ‖HH c m u‖ ≤ C * Real.exp (-c * u) := by
  obtain ⟨C, hC0, hC⟩ := Hinf_bound 0 m c x0 hc
  refine ⟨2 * Real.pi * C, fun u hu => ?_⟩
  have h := hC u hu
  have he : Real.exp (-0 * u) / (2 * Real.pi) = 1 / (2 * Real.pi) := by simp
  have hπ := Real.pi_pos
  rw [Hinf_HH, norm_mul, Complex.norm_real, he, Real.norm_eq_abs,
    abs_of_pos (by positivity), show -(0 + c) * u = -c * u by ring] at h
  calc ‖HH c m u‖ = 2 * Real.pi * (1 / (2 * Real.pi) * ‖HH c m u‖) := by field_simp
    _ ≤ 2 * Real.pi * (C * Real.exp (-c * u)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem JJ_bound (c : ℝ) (n : ℕ) (x0 : ℝ) (hc : c < 0) :
    ∃ C : ℝ, ∀ v : ℝ, x0 ≤ v → ‖JJ c n v‖ ≤ C * Real.exp (c * v) := by
  obtain ⟨C, hC0, hC⟩ := Jinf_bound 0 n c x0 hc
  refine ⟨2 * Real.pi * C, fun v hv => ?_⟩
  have h := hC v hv
  have he : Real.exp (0 * v) / (2 * Real.pi) = 1 / (2 * Real.pi) := by simp
  have hπ := Real.pi_pos
  rw [Jinf_JJ, norm_mul, Complex.norm_real, he, Real.norm_eq_abs,
    abs_of_pos (by positivity), show (0 + c) * v = c * v by ring] at h
  calc ‖JJ c n v‖ = 2 * Real.pi * (1 / (2 * Real.pi) * ‖JJ c n v‖) := by field_simp
    _ ≤ 2 * Real.pi * (C * Real.exp (c * v)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

end F506

namespace F506

open MeasureTheory Filter Topology Set Complex
open SpikedWishart.SoftEdge

/-! ### Reality and the `s^{(m)}`, `t^{(m)}` conversions. -/

theorem rayIntegral_re_zero (c θin θout : ℝ) (h : θout = -θin) (φ : ℂ → ℂ)
    (hφ : ∀ a, φ (starRingEnd ℂ a) = starRingEnd ℂ (φ a)) :
    (rayIntegral (c : ℂ) θin θout φ).re = 0 := by
  subst h
  unfold rayIntegral
  have he : exp (((-θin : ℝ) : ℂ) * I) = (starRingEnd ℂ) (exp ((θin : ℂ) * I)) := by
    rw [← exp_conj, map_mul, conj_ofReal, conj_I]; congr 1; push_cast; ring
  have hpt : ∀ t : ℝ, φ ((c : ℂ) + (t : ℂ) * exp (((-θin : ℝ) : ℂ) * I)) * exp (((-θin : ℝ) : ℂ) * I) =
      (starRingEnd ℂ) (φ ((c : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I)) * exp ((θin : ℂ) * I)) := by
    intro t
    have h0 : (c : ℂ) + (t : ℂ) * (starRingEnd ℂ) (exp ((θin : ℂ) * I)) =
        (starRingEnd ℂ) ((c : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I)) := by simp
    rw [he, h0, hφ]
    exact (map_mul _ _ _).symm
  simp_rw [hpt]
  rw [integral_conj, Complex.sub_re, Complex.conj_re, sub_self]

theorem conj_three : (starRingEnd ℂ) (3 : ℂ) = 3 := by apply Complex.ext <;> simp

theorem HH_re (c : ℝ) (m : ℕ) (u : ℝ) : (HH c m u).re = 0 := by
  refine rayIntegral_re_zero c (Real.pi / 3) (-Real.pi / 3) (by ring) _ (fun a => ?_)
  simp only [map_mul, map_add, map_neg, map_div₀, map_pow, map_one, conj_ofReal, conj_three,
    ← exp_conj]

theorem JJ_re (c : ℝ) (n : ℕ) (v : ℝ) : (JJ c n v).re = 0 := by
  refine rayIntegral_re_zero c (-2 * Real.pi / 3) (2 * Real.pi / 3) (by ring) _ (fun a => ?_)
  simp only [map_mul, map_sub, map_div₀, map_pow, conj_ofReal, conj_three, ← exp_conj]

theorem real_of_im_zero (z : ℂ) (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (by simp) (by rw [Complex.ofReal_im, h])

theorem sFn_eq (m : ℕ) (u c : ℝ) (hc : c < 0) :
    (sFn m u : ℂ) = I * (-1 : ℂ) ^ m * ((1 / (2 * Real.pi) : ℝ) : ℂ) * HH c m u := by
  have hrot : rayIntegral (I * ((-1 : ℝ) : ℂ)) (5 * Real.pi / 6) (Real.pi / 6)
      (fun a => exp (I * (u : ℂ) * a + I * a ^ 3 / 3) / (I * a) ^ m) =
      I * rayIntegral ((-1 : ℝ) : ℂ) (Real.pi / 3) (-Real.pi / 3)
        (fun a => exp (I * (u : ℂ) * (I * a) + I * (I * a) ^ 3 / 3) / (I * (I * a)) ^ m) :=
    rayIntegral_rotate _ _ _ _ _ _ _ e56 e16
  have hfun : (fun a : ℂ => exp (I * (u : ℂ) * (I * a) + I * (I * a) ^ 3 / 3) / (I * (I * a)) ^ m) =
      fun a => (-1 : ℂ) ^ m * (exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ m)) := by
    funext a
    have h1 : I * (u : ℂ) * (I * a) + I * (I * a) ^ 3 / 3 = -(u : ℂ) * a + a ^ 3 / 3 := by
      linear_combination ((u : ℂ) * a + (I ^ 2 - 1) * a ^ 3 / 3) * I_sq
    have h2 : I * (I * a) = -a := by rw [← mul_assoc, I_mul_I]; ring
    rw [h1, h2, neg_pow]
    rcases neg_one_pow_eq_or ℂ m with h | h <;> rw [h] <;> ring
  have hv : I * ((-1 : ℝ) : ℂ) = -I := by push_cast; ring
  rw [hfun, rayIntegral_const_mul, hv] at hrot
  have hvert : rayIntegral ((-1 : ℝ) : ℂ) (Real.pi / 3) (-Real.pi / 3)
      (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ m)) = HH c m u :=
    HH_vertex m u (-1) c (by norm_num) hc
  rw [hvert] at hrot
  have hS : sFn m u = ((1 / (2 * (Real.pi : ℂ))) * (I * ((-1 : ℂ) ^ m * HH c m u))).re := by
    unfold sFn; rw [hrot]
  have hZ : ((1 / (2 * (Real.pi : ℂ))) * (I * ((-1 : ℂ) ^ m * HH c m u))).im = 0 := by
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      show (-1 : ℂ) ^ m = (((-1 : ℝ) ^ m : ℝ) : ℂ) by push_cast; ring,
      Complex.im_ofReal_mul, I_mul_im, Complex.re_ofReal_mul, HH_re, mul_zero, mul_zero]
  rw [hS, real_of_im_zero _ hZ]
  push_cast
  ring

theorem tFn_eq (n : ℕ) (v c : ℝ) :
    (tFn (n + 1) v : ℂ) = -I * (-1 : ℂ) ^ n * ((1 / (2 * Real.pi) : ℝ) : ℂ) * JJ c n v := by
  have hin : exp (((5 * Real.pi / 6 : ℝ) : ℂ) * I) = -I * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) := by
    rw [em23, e56]; ring
  have hout : exp (((Real.pi / 6 : ℝ) : ℂ) * I) = -I * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) := by
    rw [e23, e16]; ring
  have hrot : rayIntegral (-I * 0) (5 * Real.pi / 6) (Real.pi / 6)
      (fun a => exp (I * (v : ℂ) * a + I * a ^ 3 / 3) * (-I * a) ^ n) =
      -I * rayIntegral 0 (-2 * Real.pi / 3) (2 * Real.pi / 3)
        (fun a => exp (I * (v : ℂ) * (-I * a) + I * (-I * a) ^ 3 / 3) * (-I * (-I * a)) ^ n) :=
    rayIntegral_rotate _ _ _ _ _ _ _ hin hout
  have hfun : (fun a : ℂ => exp (I * (v : ℂ) * (-I * a) + I * (-I * a) ^ 3 / 3) * (-I * (-I * a)) ^ n) =
      fun a => (-1 : ℂ) ^ n * (exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n) := by
    funext a
    have h1 : I * (v : ℂ) * (-I * a) + I * (-I * a) ^ 3 / 3 = (v : ℂ) * a - a ^ 3 / 3 := by
      linear_combination (-(v : ℂ) * a - (I ^ 2 - 1) * a ^ 3 / 3) * I_sq
    have h2 : -I * (-I * a) = -a := by
      rw [show -I * (-I * a) = (I * I) * a by ring, I_mul_I]; ring
    rw [h1, h2, neg_pow]; ring
  rw [hfun, rayIntegral_const_mul, mul_zero] at hrot
  have hvert : rayIntegral 0 (-2 * Real.pi / 3) (2 * Real.pi / 3)
      (fun a => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ n) = JJ c n v := by
    rw [JJ_vertex n v c]; unfold JJ; rw [Complex.ofReal_zero]
  rw [hvert] at hrot
  have hS : tFn (n + 1) v = ((1 / (2 * (Real.pi : ℂ))) * (-I * ((-1 : ℂ) ^ n * JJ c n v))).re := by
    unfold tFn; rw [Nat.add_sub_cancel, hrot]
  have hZ : ((1 / (2 * (Real.pi : ℂ))) * (-I * ((-1 : ℂ) ^ n * JJ c n v))).im = 0 := by
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      show (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) by push_cast; ring,
      Complex.im_ofReal_mul, neg_mul, Complex.neg_im, I_mul_im, Complex.re_ofReal_mul, JJ_re,
      mul_zero, neg_zero, mul_zero]
  rw [hS, real_of_im_zero _ hZ]
  push_cast
  ring

/-! ### Assembly. -/

theorem prod_eq (ε : ℝ) (k : ℕ) (c c' u v y : ℝ) :
    Hinf ε k c (u + y) * Jinf ε k c' (v + y) =
      ((Real.exp (-ε * u) * Real.exp (ε * v) / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
        (HH c k (u + y) * JJ c' k (v + y)) := by
  rw [Hinf_HH, Jinf_JJ]
  have hE : Real.exp (-ε * (u + y)) * Real.exp (ε * (v + y)) =
      Real.exp (-ε * u) * Real.exp (ε * v) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hE' := congrArg (fun r : ℝ => (r : ℂ)) hE
  simp only [Complex.ofReal_mul] at hE'
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  linear_combination (HH c k (u + y) * JJ c' k (v + y) / (2 * (Real.pi : ℂ)) ^ 2) * hE'

theorem tele (k : ℕ) (f : ℕ → ℂ) : ∑ m ∈ Finset.Icc 1 k, (f m - f (m - 1)) = f k - f 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

theorem core (E : ℂ) (H J : ℕ → ℝ → ℂ) (cH cJ u v : ℝ) (hδ : cJ < cH) (k : ℕ)
    (hH : ∀ m w, HasDerivAt (H (m + 1)) (-H m w) w) (hJ : ∀ n w, HasDerivAt (J n) (J (n + 1) w) w)
    (hHb : ∀ m, ∃ C, ∀ w, u ≤ w → ‖H m w‖ ≤ C * Real.exp (-cH * w))
    (hJb : ∀ n, ∃ C, ∀ w, v ≤ w → ‖J n w‖ ≤ C * Real.exp (cJ * w))
    (hHm : ∀ m, Measurable (H m)) (hJc : ∀ n, Continuous (J n)) :
    (∫ y in Ioi (0 : ℝ), E * (H k (u + y) * J k (v + y))) -
        (∫ y in Ioi (0 : ℝ), E * (H 0 (u + y) * J 0 (v + y))) =
      -(E * ∑ m ∈ Finset.Icc 1 k, H m u * J (m - 1) v) := by
  have hδ' : 0 < cH - cJ := by linarith
  have hP : ∀ m n, ∃ K, ∀ y, 0 ≤ y → ‖H m (u + y) * J n (v + y)‖ ≤ K * Real.exp (-(cH - cJ) * y) := by
    intro m n
    obtain ⟨C1, hC1⟩ := hHb m
    obtain ⟨C2, hC2⟩ := hJb n
    refine ⟨|C1| * |C2| * Real.exp (-cH * u + cJ * v), fun y hy => ?_⟩
    rw [norm_mul]
    have h1 := (hC1 (u + y) (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C1) (Real.exp_pos _).le)
    have h2 := (hC2 (v + y) (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le)
    have he : Real.exp (-cH * (u + y)) * Real.exp (cJ * (v + y)) =
        Real.exp (-cH * u + cJ * v) * Real.exp (-(cH - cJ) * y) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc ‖H m (u + y)‖ * ‖J n (v + y)‖ ≤
          (|C1| * Real.exp (-cH * (u + y))) * (|C2| * Real.exp (cJ * (v + y))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = |C1| * |C2| * (Real.exp (-cH * (u + y)) * Real.exp (cJ * (v + y))) := by ring
      _ = _ := by rw [he]; ring
  have hI : ∀ m n, Integrable (fun y => E * (H m (u + y) * J n (v + y))) (volume.restrict (Ioi 0)) := by
    intro m n
    obtain ⟨K, hK⟩ := hP m n
    have hmeas : Measurable fun y => H m (u + y) * J n (v + y) :=
      ((hHm m).comp (measurable_const_add u)).mul ((hJc n).measurable.comp (measurable_const_add v))
    refine Integrable.const_mul ?_ E
    refine Integrable.mono' (Integrable.const_mul (exp_neg_integrableOn_Ioi 0 hδ') K)
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun y hy => hK y (le_of_lt hy)
  have hGd : ∀ y, HasDerivAt (fun y => ∑ m ∈ Finset.Icc 1 k, H m (u + y) * J (m - 1) (v + y))
      (H k (u + y) * J k (v + y) - H 0 (u + y) * J 0 (v + y)) y := by
    intro y
    have hterm : ∀ m ∈ Finset.Icc 1 k, HasDerivAt (fun y => H m (u + y) * J (m - 1) (v + y))
        (H m (u + y) * J m (v + y) - H (m - 1) (u + y) * J (m - 1) (v + y)) y := by
      intro m hm
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by have := (Finset.mem_Icc.1 hm).1; omega⟩
      have h1 := (hH j (u + y)).comp_const_add u y
      have h2 := (hJ j (v + y)).comp_const_add v y
      simp only [Nat.add_sub_cancel]
      exact (h1.mul h2).congr_deriv (by ring)
    exact (HasDerivAt.fun_sum hterm).congr_deriv (tele k (fun m => H m (u + y) * J m (v + y)))
  have hGlim : Tendsto (fun y => ∑ m ∈ Finset.Icc 1 k, H m (u + y) * J (m - 1) (v + y))
      atTop (𝓝 0) := by
    have h0 : (0 : ℂ) = ∑ m ∈ Finset.Icc 1 k, (0 : ℂ) := by simp
    rw [h0]
    refine tendsto_finset_sum _ fun m _ => ?_
    obtain ⟨K, hK⟩ := hP m (m - 1)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hT : Tendsto (fun y : ℝ => K * Real.exp (-(cH - cJ) * y)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => -(cH - cJ) * y) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul K
    refine squeeze_zero' (Filter.Eventually.of_forall fun y => norm_nonneg _) ?_ hT
    filter_upwards [Filter.eventually_ge_atTop 0] with y hy
    exact hK y hy
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y => E * ∑ m ∈ Finset.Icc 1 k, H m (u + y) * J (m - 1) (v + y))
    (f' := fun y => E * (H k (u + y) * J k (v + y)) - E * (H 0 (u + y) * J 0 (v + y)))
    (a := 0) (m := E * 0)
    (((hGd 0).const_mul E).continuousAt.continuousWithinAt)
    (fun y _ => ((hGd y).const_mul E).congr_deriv (by ring))
    (Integrable.sub (hI k k) (hI 0 0))
    (hGlim.const_mul E)
  rw [← integral_sub (hI k k) (hI 0 0), hFTC]
  simp only [add_zero, mul_zero, zero_sub]

theorem eq200_main (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (cH cJ : ℝ) (hcH0 : -ε < cH)
    (hcH1 : cH < 0) (hcJ : cJ < -ε) (u v : ℝ) :
    (∫ y in Set.Ioi (0 : ℝ), Hinf ε k cH (u + y) * Jinf ε k cJ (v + y)) -
        (∫ y in Set.Ioi (0 : ℝ),
          ((Real.exp (-ε * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (ε * (v + y)) : ℝ) : ℂ)) =
      ∑ m ∈ Finset.Icc 1 k,
        ((Real.exp (-ε * u) * sFn m u * tFn m v * Real.exp (ε * v) : ℝ) : ℂ) := by
  have hcJ0 : cJ < 0 := by linarith
  have hB : ∀ y : ℝ, ((Real.exp (-ε * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (ε * (v + y)) : ℝ) : ℂ) =
      ((Real.exp (-ε * u) * Real.exp (ε * v) / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
        (HH cH 0 (u + y) * JJ cJ 0 (v + y)) := fun y => by
    rw [← Hinf_Jinf_zero ε cH cJ (u + y) (v + y), prod_eq]
  simp_rw [prod_eq ε k cH cJ u v, hB]
  rw [core _ (HH cH) (JJ cJ) cH cJ u v (by linarith) k (fun m w => HH_hasDerivAt cH m hcH1 w)
    (fun n w => JJ_hasDerivAt cJ n hcJ0 w) (fun m => HH_bound cH m u hcH1)
    (fun n => JJ_bound cJ n v hcJ0) (fun m => HH_measurable cH m hcH1)
    (fun n => JJ_continuous cJ n hcJ0)]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by have := (Finset.mem_Icc.1 hm).1; omega⟩
  simp only [Nat.add_sub_cancel]
  have hsq : ((-1 : ℂ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul, sFn_eq (j + 1) u cH hcH1,
    tFn_eq j v cJ, pow_succ]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_one]
  set e1 : ℂ := ((Real.exp (-ε * u) : ℝ) : ℂ)
  set e2 : ℂ := ((Real.exp (ε * v) : ℝ) : ℂ)
  set P : ℂ := (-1 : ℂ) ^ j
  set Hh : ℂ := HH cH (j + 1) u
  set Jj : ℂ := JJ cJ j v
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  linear_combination (-(e1 * e2 * Hh * Jj / (2 * (Real.pi : ℂ)) ^ 2) * P ^ 2) * I_sq +
    (e1 * e2 * Hh * Jj / (2 * (Real.pi : ℂ)) ^ 2) * hsq

end F506

open MeasureTheory SpikedWishart.SoftEdge in
theorem solution (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (cH cJ : ℝ) (hcH0 : -ε < cH)
    (hcH1 : cH < 0) (hcJ : cJ < -ε) (u v : ℝ) :
    (∫ y in Set.Ioi (0 : ℝ), Hinf ε k cH (u + y) * Jinf ε k cJ (v + y)) -
        (∫ y in Set.Ioi (0 : ℝ),
          ((Real.exp (-ε * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (ε * (v + y)) : ℝ) : ℂ)) =
      ∑ m ∈ Finset.Icc 1 k,
        ((Real.exp (-ε * u) * sFn m u * tFn m v * Real.exp (ε * v) : ℝ) : ℂ) := by
  exact F506.eq200_main k hk ε hε cH cJ hcH0 hcH1 hcJ u v
