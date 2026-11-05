-- Prove2me | solution 1 for SpikedWishart.SoftEdge.Jinf_vertex_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:48:44.535003+00:00
-- url     : https://prove2.me/submissions/772e906f-3096-47bd-807e-9b10ff52a47f

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option linter.all false
set_option Elab.async false

set_option autoImplicit false

namespace P31J4

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


/-- Derivative of the `𝓙_∞` integrand `e^{va - a³/3} a^k`. -/
noncomputable def phiJd (v : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  exp ((v : ℂ) * z - z ^ 3 / 3) * (((v : ℂ) - z ^ 2) * z ^ k + (k : ℂ) * z ^ (k - 1))

theorem phiJ_hasDerivAt (v : ℝ) (k : ℕ) (z : ℂ) :
    HasDerivAt (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k) (phiJd v k z) z := by
  have h1 : HasDerivAt (fun a : ℂ => (v : ℂ) * a - a ^ 3 / 3)
      ((v : ℂ) * 1 - ((3 : ℕ) * z ^ (3 - 1)) / 3) z :=
    ((hasDerivAt_id' z).const_mul _).sub ((hasDerivAt_pow 3 z).div_const 3)
  have h2 := h1.cexp.mul (hasDerivAt_pow k z)
  refine h2.congr_deriv ?_
  unfold phiJd
  norm_num
  ring

theorem phiJd_continuous (v : ℝ) (k : ℕ) : Continuous (phiJd v k) := by
  unfold phiJd; fun_prop

/-- Exponential decay of the `𝓙_∞` integrand and its derivative on the rays `cos θ = -1/2`,
uniformly for real vertices `|s| ≤ R`. -/
theorem phiJ_ray_bound2 (v θ : ℝ) (hcos : Real.cos θ = -(1 / 2)) (hsin : Real.sin θ ^ 2 = 3 / 4)
    (k : ℕ) (R : ℝ) :
    ∃ B : ℝ, ∀ s : ℝ, |s| ≤ R → ∀ t : ℝ, 0 < t →
      ‖(fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k)
          ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖phiJd v k ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) := by
  obtain ⟨D, hD⟩ := cubic_bound (|v| / 2 + R ^ 2 / 2 + (k : ℝ) + 2) (R / 2)
  refine ⟨(|v| + 2 + k) * Real.exp (|v| * R + R ^ 3 / 3 + ((k : ℝ) + 1) * R + D),
    fun s hs t ht => ?_⟩
  have hR : 0 ≤ R := (abs_nonneg s).trans hs
  set a : ℂ := (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  have hre : a.re = s - t / 2 := by
    rw [ha, Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im, hcos]; ring
  have him : a.im = t * Real.sin θ := by
    rw [ha, Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]; ring
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  have hwre : ((v : ℂ) * a - a ^ 3 / 3).re =
      v * s - v * t / 2 - s ^ 3 / 3 + s ^ 2 / 2 * t + s / 2 * t ^ 2 - t ^ 3 / 3 := by
    rw [Complex.sub_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, ofReal_re, ofReal_im,
      him2, hre]
    ring
  have hn0 : 0 ≤ ‖a‖ := norm_nonneg a
  have hL : ‖a‖ ≤ t + R := by
    have h1 := norm_add_le (s : ℂ) ((t : ℂ) * exp ((θ : ℂ) * I))
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, norm_real, Real.norm_of_nonneg ht.le,
      Real.norm_eq_abs] at h1
    rw [ha]; linarith
  set L : ℝ := t + R with hLdef
  have hL0 : 0 ≤ L := by linarith
  have heL : 1 ≤ Real.exp L := Real.one_le_exp hL0
  have hpow : ∀ j : ℕ, j ≤ k → ‖a ^ j‖ ≤ Real.exp ((k : ℝ) * L) := by
    intro j hj
    rw [norm_pow, Real.exp_nat_mul]
    have h1 : ‖a‖ ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc ‖a‖ ^ j ≤ Real.exp L ^ j := pow_le_pow_left₀ hn0 h1 j
      _ ≤ Real.exp L ^ k := pow_le_pow_right₀ heL hj
  have hsq : ‖(v : ℂ) - a ^ 2‖ ≤ |v| + 2 * Real.exp L := by
    have h1 := norm_sub_le (v : ℂ) (a ^ 2)
    rw [norm_real, Real.norm_eq_abs, norm_pow] at h1
    have h2 : ‖a‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hn0 hL 2
    have h3 := Real.quadratic_le_exp_of_nonneg hL0
    linarith
  have hvs : v * s ≤ |v| * R := by
    have h1 : v * s ≤ |v * s| := le_abs_self _
    rw [abs_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hs (abs_nonneg v))
  have hvt : -v * t ≤ |v| * t := mul_le_mul_of_nonneg_right (by linarith [neg_abs_le v]) ht.le
  have hs3 : -s ^ 3 ≤ R ^ 3 := by
    have h1 : -s ^ 3 ≤ |s ^ 3| := neg_le_abs _
    rw [abs_pow] at h1
    exact h1.trans (pow_le_pow_left₀ (abs_nonneg s) hs 3)
  have hs2 : s ^ 2 * t ≤ R ^ 2 * t := by
    have h1 : s ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg s) hs 2
    exact mul_le_mul_of_nonneg_right h1 ht.le
  have hst : s * t ^ 2 ≤ R * t ^ 2 :=
    mul_le_mul_of_nonneg_right ((le_abs_self s).trans hs) (sq_nonneg t)
  have hexp : ((v : ℂ) * a - a ^ 3 / 3).re + ((k : ℝ) + 1) * L ≤
      (|v| * R + R ^ 3 / 3 + ((k : ℝ) + 1) * R + D) + -t := by
    rw [hwre, hLdef]
    have h1 := hD t ht.le
    linarith
  have hC : 0 ≤ |v| + 2 + (k : ℝ) := by positivity
  have hE : Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) * Real.exp ((k : ℝ) * L) * Real.exp L ≤
      Real.exp (|v| * R + R ^ 3 / 3 + ((k : ℝ) + 1) * R + D) * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hEpos : 0 ≤ Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) := (Real.exp_pos _).le
  have hkpos : 0 ≤ Real.exp ((k : ℝ) * L) := (Real.exp_pos _).le
  constructor
  · show ‖exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k‖ ≤ _
    rw [norm_mul, norm_exp]
    calc Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) * ‖a ^ k‖
        ≤ Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) * Real.exp ((k : ℝ) * L) * 1 := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left (hpow k le_rfl) hEpos
      _ ≤ (|v| + 2 + k) * (Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) *
            Real.exp ((k : ℝ) * L) * Real.exp L) := by
          have h1 : 1 ≤ (|v| + 2 + k) * Real.exp L := by nlinarith [abs_nonneg v]
          have h2 : 0 ≤ Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) * Real.exp ((k : ℝ) * L) :=
            mul_nonneg hEpos hkpos
          nlinarith
      _ ≤ _ := (mul_le_mul_of_nonneg_left hE hC).trans_eq (by ring)
  · unfold phiJd
    rw [norm_mul, norm_exp]
    have hk1 : ‖((v : ℂ) - a ^ 2) * a ^ k + (k : ℂ) * a ^ (k - 1)‖ ≤
        (|v| + 2 + k) * (Real.exp ((k : ℝ) * L) * Real.exp L) := by
      have h1 := norm_add_le (((v : ℂ) - a ^ 2) * a ^ k) ((k : ℂ) * a ^ (k - 1))
      rw [norm_mul, norm_mul, Complex.norm_natCast] at h1
      have h2 : ‖(v : ℂ) - a ^ 2‖ * ‖a ^ k‖ ≤ (|v| + 2 * Real.exp L) * Real.exp ((k : ℝ) * L) :=
        mul_le_mul hsq (hpow k le_rfl) (norm_nonneg _) (by positivity)
      have h3 : (k : ℝ) * ‖a ^ (k - 1)‖ ≤ (k : ℝ) * Real.exp ((k : ℝ) * L) :=
        mul_le_mul_of_nonneg_left (hpow (k - 1) (Nat.sub_le k 1)) (Nat.cast_nonneg k)
      have h4 : |v| * Real.exp ((k : ℝ) * L) ≤ |v| * (Real.exp ((k : ℝ) * L) * Real.exp L) := by
        have := mul_le_mul_of_nonneg_left heL hkpos
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg v)
      have h5 : (k : ℝ) * Real.exp ((k : ℝ) * L) ≤ (k : ℝ) * (Real.exp ((k : ℝ) * L) * Real.exp L) := by
        have := mul_le_mul_of_nonneg_left heL hkpos
        exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)
      nlinarith
    calc Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) * ‖((v : ℂ) - a ^ 2) * a ^ k + (k : ℂ) * a ^ (k - 1)‖
        ≤ Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) *
            ((|v| + 2 + k) * (Real.exp ((k : ℝ) * L) * Real.exp L)) :=
          mul_le_mul_of_nonneg_left hk1 hEpos
      _ = (|v| + 2 + k) * (Real.exp (((v : ℂ) * a - a ^ 3 / 3).re) *
            Real.exp ((k : ℝ) * L) * Real.exp L) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hE hC).trans_eq (by ring)

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem sin_two_pi_div_three_sq : Real.sin (2 * Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three,
    div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem cos_neg_two_pi_div_three : Real.cos (-2 * Real.pi / 3) = -(1 / 2) := by
  rw [show -2 * Real.pi / 3 = -(2 * Real.pi / 3) by ring, Real.cos_neg, cos_two_pi_div_three]

theorem sin_neg_two_pi_div_three_sq : Real.sin (-2 * Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [show -2 * Real.pi / 3 = -(2 * Real.pi / 3) by ring, Real.sin_neg, neg_sq,
    sin_two_pi_div_three_sq]

/-- `𝓙_∞` does not depend on its real vertex (the integrand is entire). -/
theorem Jinf_vertex (ε : ℝ) (k : ℕ) (c c' v : ℝ) : Jinf ε k c v = Jinf ε k c' v := by
  unfold Jinf
  have key := fun p : ℝ => rayIntegral_vertex_indep
    (fun a : ℂ => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k) (phiJd v k) (phiJ_hasDerivAt v k)
    (phiJd_continuous v k) (-2 * Real.pi / 3) (2 * Real.pi / 3)
    (phiJ_ray_bound2 v _ cos_neg_two_pi_div_three sin_neg_two_pi_div_three_sq k)
    (phiJ_ray_bound2 v _ cos_two_pi_div_three sin_two_pi_div_three_sq k) p
  rw [key c, key c']

end P31J4

open Complex MeasureTheory SpikedWishart.SoftEdge in
theorem solution :
    ∀ (ε : ℝ) (k : ℕ) (c c' v : ℝ), Jinf ε k c v = Jinf ε k c' v := by
  exact P31J4.Jinf_vertex
