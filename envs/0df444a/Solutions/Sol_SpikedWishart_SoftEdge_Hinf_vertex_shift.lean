-- Prove2me | solution 1 for SpikedWishart.SoftEdge.Hinf_vertex_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T08:14:24.872973+00:00
-- url     : https://prove2.me/submissions/3665344e-71c7-4b62-845f-be1d12f38c4f

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option linter.all false
set_option Elab.async false


set_option autoImplicit false

namespace P31K1

open MeasureTheory Filter Topology Set Complex

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

/-- Differentiation of a ray integral in its real vertex, local version (the integrand only needs
to be holomorphic on an open set `U` containing the rays from nearby vertices). -/
theorem ray_deriv_loc (φ φ' : ℂ → ℂ) (U : Set ℂ) (hφ : ∀ z ∈ U, HasDerivAt φ (φ' z) z)
    (hφ'c : ContinuousOn φ' U) (θ s0 r B : ℝ) (hr : 0 < r)
    (hU : ∀ s : ℝ, |s - s0| < r → ∀ t : ℝ, 0 ≤ t → (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) ∈ U)
    (hB : ∀ s : ℝ, |s - s0| < r → ∀ t : ℝ, 0 < t →
      ‖φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t)) :
    HasDerivAt (fun s : ℝ => ∫ t in Ioi (0 : ℝ),
      φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) (-φ s0) s0 := by
  have hcont : ContinuousOn φ U := fun z hz => (hφ z hz).continuousAt.continuousWithinAt
  have hω : ‖exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  have hline : ∀ s : ℝ, Continuous fun t : ℝ => (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) :=
    fun s => continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hs0 : |s0 - s0| < r := by simpa using hr
  have hc0 : ∀ s : ℝ, |s - s0| < r →
      ContinuousOn (fun t : ℝ => φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))) (Ici 0) :=
    fun s hs => hcont.comp (hline s).continuousOn (fun t ht => hU s hs t ht)
  have hcl : ∀ s : ℝ, |s - s0| < r → ContinuousOn
      (fun t : ℝ => φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) (Ici 0) :=
    fun s hs => (hc0 s hs).mul continuousOn_const
  have hcl' : ContinuousOn
      (fun t : ℝ => φ' ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) (Ici 0) :=
    (hφ'c.comp (hline s0).continuousOn (fun t ht => hU s0 hs0 t ht)).mul continuousOn_const
  have hbi : Integrable (fun t : ℝ => B * Real.exp (-t)) (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) B
  have hball : ∀ s ∈ Metric.ball s0 r, |s - s0| < r := fun s hs => by
    rwa [Metric.mem_ball, Real.dist_eq] at hs
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℝ) (t : ℝ) => φ ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
    (F' := fun (s : ℝ) (t : ℝ) => φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I))
    (x₀ := s0) (bound := fun t => B * Real.exp (-t)) (s := Metric.ball s0 r)
    (Metric.ball_mem_nhds s0 hr)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds s0 hr) (fun s hs =>
      ((hcl s (hball s hs)).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi))
    (by
      refine hbi.mono' (((hcl s0 hs0).mono Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      show ‖φ ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B * Real.exp (-t)
      rw [norm_mul, hω, mul_one]
      exact (hB s0 hs0 t ht).1)
    ((hcl'.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht s hs => ?_)
      show ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)‖ ≤ B * Real.exp (-t)
      rw [norm_mul, hω, mul_one]
      exact (hB s (hball s hs) t ht).2)
    hbi
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht s hs => ?_)
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) 1 s :=
        ((hasDerivAt_id' (s : ℂ)).comp_ofReal).add_const _
      have h2 := ((hφ _ (hU s (hball s hs) t (le_of_lt ht))).comp s h1).mul_const
        (exp ((θ : ℂ) * I))
      rw [mul_one] at h2
      exact h2)
  have hval : ∫ t in Ioi (0 : ℝ), φ' ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I) =
      -φ s0 := by
    have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => φ ((s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I)))
        (φ' ((s0 : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) t := by
      intro t ht
      have h1 : HasDerivAt (fun y : ℝ => (s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I))
          (exp ((θ : ℂ) * I)) t := by
        have := (((hasDerivAt_id' (t : ℂ)).comp_ofReal).mul_const (exp ((θ : ℂ) * I))).const_add
          (s0 : ℂ)
        rw [one_mul] at this
        exact this
      exact (hφ _ (hU s0 hs0 t (le_of_lt ht))).comp t h1
    have hlim : Tendsto (fun y : ℝ => φ ((s0 : ℂ) + (y : ℂ) * exp ((θ : ℂ) * I))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hE : Tendsto (fun y : ℝ => B * Real.exp (-y)) atTop (𝓝 0) := by
        simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul B)
      refine squeeze_zero' (Filter.Eventually.of_forall (fun y => norm_nonneg _)) ?_ hE
      filter_upwards [Filter.eventually_gt_atTop 0] with y hy
      exact (hB s0 hs0 y hy).1
    have := integral_Ioi_of_hasDerivAt_of_tendsto
      ((hc0 s0 hs0) 0 (Set.mem_Ici.2 le_rfl)) hd key.1 hlim
    rw [this]
    simp
  rw [← hval]
  exact key.2

/-- The broken-line integral is constant in its real vertex on an open preconnected set of
vertices, given local holomorphy and local uniform exponential bounds. -/
theorem rayIntegral_vertex_const (φ φ' : ℂ → ℂ) (U : Set ℂ) (hφ : ∀ z ∈ U, HasDerivAt φ (φ' z) z)
    (hφ'c : ContinuousOn φ' U) (θin θout : ℝ) (S : Set ℝ) (hS : IsOpen S) (hS' : IsPreconnected S)
    (hloc : ∀ s0 ∈ S, ∃ r B : ℝ, 0 < r ∧
      (∀ s : ℝ, |s - s0| < r → ∀ t : ℝ, 0 ≤ t →
        (s : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I) ∈ U ∧ (s : ℂ) + (t : ℂ) * exp ((θout : ℂ) * I) ∈ U) ∧
      (∀ s : ℝ, |s - s0| < r → ∀ t : ℝ, 0 < t →
        (‖φ ((s : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
          ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θin : ℂ) * I))‖ ≤ B * Real.exp (-t)) ∧
        (‖φ ((s : ℂ) + (t : ℂ) * exp ((θout : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
          ‖φ' ((s : ℂ) + (t : ℂ) * exp ((θout : ℂ) * I))‖ ≤ B * Real.exp (-t))))
    {p q : ℝ} (hp : p ∈ S) (hq : q ∈ S) :
    SpikedWishart.SoftEdge.rayIntegral (p : ℂ) θin θout φ =
      SpikedWishart.SoftEdge.rayIntegral (q : ℂ) θin θout φ := by
  have hD : ∀ s ∈ S, HasDerivAt
      (fun s : ℝ => SpikedWishart.SoftEdge.rayIntegral (s : ℂ) θin θout φ) 0 s := by
    intro s0 hs0
    obtain ⟨r, B, hr, hU, hB⟩ := hloc s0 hs0
    have h := (ray_deriv_loc φ φ' U hφ hφ'c θout s0 r B hr (fun s hs t ht => (hU s hs t ht).2)
      (fun s hs t ht => (hB s hs t ht).2)).sub
      (ray_deriv_loc φ φ' U hφ hφ'c θin s0 r B hr (fun s hs t ht => (hU s hs t ht).1)
      (fun s hs t ht => (hB s hs t ht).1))
    rw [sub_self] at h
    exact h
  exact hS.is_const_of_deriv_eq_zero hS'
    (fun s hs => (hD s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hD s hs).deriv) hp hq

/-- The `𝓗_∞` integrand and its derivative. -/
noncomputable def phiH (u : ℝ) (k : ℕ) (a : ℂ) : ℂ := exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k)

noncomputable def phiH' (u : ℝ) (k : ℕ) (a : ℂ) : ℂ :=
  exp (-(u : ℂ) * a + a ^ 3 / 3) * ((-(u : ℂ) + a ^ 2) * (1 / a ^ k) - (k : ℂ) * (1 / a ^ k) * (1 / a))

theorem phiH_hasDerivAt (u : ℝ) (k : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (phiH u k) (phiH' u k z) z := by
  have h0 : HasDerivAt (fun a : ℂ => -(u : ℂ) * a + a ^ 3 / 3)
      (-(u : ℂ) * 1 + ((3 : ℕ) * z ^ (3 - 1)) / 3) z :=
    ((hasDerivAt_id' z).const_mul _).add ((hasDerivAt_pow 3 z).div_const 3)
  have h1 : HasDerivAt (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3))
      (exp (-(u : ℂ) * z + z ^ 3 / 3) * (-(u : ℂ) + z ^ 2)) z :=
    h0.cexp.congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun a : ℂ => 1 / a ^ k) (-(k : ℂ) * (1 / z ^ k) * (1 / z)) z := by
    have h : HasDerivAt (fun a : ℂ => (a ^ k)⁻¹) (-((k : ℂ) * z ^ (k - 1)) / (z ^ k) ^ 2) z :=
      (hasDerivAt_pow k z).inv (pow_ne_zero k hz)
    have heq : -((k : ℂ) * z ^ (k - 1)) / (z ^ k) ^ 2 = -(k : ℂ) * (z ^ k)⁻¹ * z⁻¹ := by
      rcases k with _ | n
      · simp
      · rw [Nat.add_sub_cancel]
        field_simp
        ring
    simp only [one_div]
    exact h.congr_deriv heq
  have h3 := h1.mul h2
  unfold phiH phiH'
  exact h3.congr_deriv (by ring)

theorem phiH'_contOn (u : ℝ) (k : ℕ) : ContinuousOn (phiH' u k) {z : ℂ | z ≠ 0} := by
  have hinv : ContinuousOn (fun a : ℂ => 1 / a ^ k) {z : ℂ | z ≠ 0} :=
    continuousOn_const.div (continuousOn_id.pow k) (fun z hz => pow_ne_zero k hz)
  have hinv1 : ContinuousOn (fun a : ℂ => 1 / a) {z : ℂ | z ≠ 0} :=
    continuousOn_const.div continuousOn_id (fun z hz => hz)
  have hE : Continuous (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3)) := by fun_prop
  have hP : Continuous (fun a : ℂ => -(u : ℂ) + a ^ 2) := by fun_prop
  exact hE.continuousOn.mul ((hP.continuousOn.mul hinv).sub
    ((continuousOn_const.mul hinv).mul hinv1))

/-- Geometry of a ray at angle `±π/3` from a negative vertex. -/
theorem ray_geom (u s t θ : ℝ) (hcos : Real.cos θ = 1 / 2) (hsin : Real.sin θ ^ 2 = 3 / 4)
    (hs : s < 0) (ht : 0 ≤ t) :
    -s / 2 ≤ ‖(s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)‖ ∧
      ‖(s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)‖ ≤ -s + t ∧
      (-(u : ℂ) * ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) +
        ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3).re =
        -u * s - u * t / 2 + s ^ 3 / 3 + s ^ 2 * t / 2 - s * t ^ 2 / 2 - t ^ 3 / 3 := by
  set a : ℂ := (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hre, him⟩ := ray_point_re_im s t θ
  rw [← ha] at hre him
  rw [hcos] at hre
  have him2 : a.im ^ 2 = 3 / 4 * t ^ 2 := by rw [him, mul_pow, hsin]; ring
  refine ⟨?_, ?_, ?_⟩
  · have hnorm2 : (-s / 2) ^ 2 ≤ ‖a‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre]
      nlinarith [sq_nonneg (t + s / 2), him2, sq_nonneg a.im]
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (norm_nonneg a) hlt
    nlinarith
  · calc ‖a‖ ≤ ‖(s : ℂ)‖ + ‖(t : ℂ) * exp ((θ : ℂ) * I)‖ := norm_add_le _ _
      _ = -s + t := by
        rw [norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hs, abs_of_nonneg ht, mul_one]
  · rw [Complex.add_re, Complex.div_ofNat_re, re_cube, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, ofReal_re, ofReal_im, him2, hre]
    ring

set_option maxHeartbeats 1000000 in
/-- Uniform local bounds for the `𝓗_∞` integrand and its derivative on rays at `±π/3`. -/
theorem phiH_bounds (u : ℝ) (k : ℕ) (θ : ℝ) (hcos : Real.cos θ = 1 / 2)
    (hsin : Real.sin θ ^ 2 = 3 / 4) (s0 : ℝ) (hs0 : s0 < 0) :
    ∃ B : ℝ, ∀ s : ℝ, |s - s0| < -s0 / 2 → ∀ t : ℝ, 0 < t →
      ‖phiH u k ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) ∧
      ‖phiH' u k ((s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I))‖ ≤ B * Real.exp (-t) := by
  set L : ℝ := -2 * s0 with hL
  set m : ℝ := -s0 / 4 with hm
  have hm0 : 0 < m := by rw [hm]; linarith only [hs0]
  have hL0 : 0 < L := by rw [hL]; linarith only [hm, hm0]
  obtain ⟨D, hD⟩ := cubic_bound (|u| / 2 + L ^ 2 / 2 + 2) (L / 2)
  set P : ℝ := ((|u| + 2 * L ^ 2 + 4) + k / m) * (1 / m) ^ k with hP
  refine ⟨P * Real.exp (|u| * L + D), fun s hs t ht => ?_⟩
  obtain ⟨hs1, hs2⟩ := abs_lt.1 hs
  have hsneg : s < 0 := by linarith only [hs1, hs2]
  set a : ℂ := (s : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) with ha
  obtain ⟨hlo, hhi, hre⟩ := ray_geom u s t θ hcos hsin hsneg ht.le
  rw [← ha] at hlo hhi hre
  have hma : m ≤ ‖a‖ := by rw [hm]; linarith only [hs2, hlo]
  have hapos : 0 < ‖a‖ := lt_of_lt_of_le hm0 hma
  have haL : ‖a‖ ≤ L + t := by rw [hL]; linarith only [hs1, hsneg, hhi]
  -- exponent
  have hsL : -s ≤ L := by rw [hL]; linarith only [hs1, hsneg]
  have hexp : (-(u : ℂ) * a + a ^ 3 / 3).re ≤ |u| * L + D - 2 * t := by
    rw [hre]
    have h1 := hD t ht.le
    have hu1 : -u * s ≤ |u| * L := by
      have : -u * s = u * (-s) := by ring
      rw [this]
      calc u * (-s) ≤ |u| * (-s) := mul_le_mul_of_nonneg_right (le_abs_self u) (by linarith only [hsneg])
        _ ≤ |u| * L := mul_le_mul_of_nonneg_left hsL (abs_nonneg u)
    have hu2 : -u * t / 2 ≤ |u| * t / 2 := by
      have := mul_le_mul_of_nonneg_right (neg_le_abs u) ht.le
      linarith only [this]
    have hs3 : s ^ 3 / 3 ≤ 0 := by
      have : s ^ 3 = s * s ^ 2 := by ring
      rw [this]
      have := mul_nonpos_of_nonpos_of_nonneg hsneg.le (sq_nonneg s)
      linarith only [this]
    have hs2' : s ^ 2 ≤ L ^ 2 := by nlinarith
    have hs4 : s ^ 2 * t / 2 ≤ L ^ 2 * t / 2 := by
      have := mul_le_mul_of_nonneg_right hs2' ht.le
      linarith only [this]
    have hs5 : -s * t ^ 2 / 2 ≤ L * t ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_right hsL (sq_nonneg t)
      linarith only [this]
    nlinarith
  have hk : ‖1 / a ^ k‖ ≤ (1 / m) ^ k := by
    rw [norm_div, norm_one, norm_pow, ← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hm0 hma) k
  have h1a : ‖1 / a‖ ≤ 1 / m := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hm0 hma
  have het : 1 ≤ Real.exp t := Real.one_le_exp ht.le
  have hq := Real.quadratic_le_exp_of_nonneg ht.le
  have hpoly : ‖-(u : ℂ) + a ^ 2‖ ≤ (|u| + 2 * L ^ 2 + 4) * Real.exp t := by
    calc ‖-(u : ℂ) + a ^ 2‖ ≤ ‖-(u : ℂ)‖ + ‖a ^ 2‖ := norm_add_le _ _
      _ = |u| + ‖a‖ ^ 2 := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      _ ≤ |u| + (L + t) ^ 2 := by
          have := pow_le_pow_left₀ (norm_nonneg a) haL 2
          linarith only [this]
      _ ≤ (|u| + 2 * L ^ 2 + 4) * Real.exp t := by
          have hu0 := abs_nonneg u
          nlinarith [sq_nonneg (L - t)]
  have hEexp : Real.exp ((-(u : ℂ) * a + a ^ 3 / 3).re) * Real.exp t ≤
      Real.exp (|u| * L + D) * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith only [hexp])
  have hEexp' : Real.exp ((-(u : ℂ) * a + a ^ 3 / 3).re) ≤
      Real.exp (|u| * L + D) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith only [ht, hexp])
  have hPk : (1 / m) ^ k ≤ P := by
    rw [hP]
    have h0 : 0 ≤ (1 / m) ^ k := by positivity
    have : 1 ≤ (|u| + 2 * L ^ 2 + 4) + k / m := by
      have := abs_nonneg u
      have : 0 ≤ (k : ℝ) / m := by positivity
      nlinarith [sq_nonneg L]
    nlinarith
  have hP0 : 0 ≤ P := le_trans (by positivity) hPk
  have hE0 : 0 ≤ Real.exp (|u| * L + D) * Real.exp (-t) := by positivity
  constructor
  · unfold phiH
    rw [norm_mul, norm_exp]
    calc Real.exp ((-(u : ℂ) * a + a ^ 3 / 3).re) * ‖1 / a ^ k‖
        ≤ (Real.exp (|u| * L + D) * Real.exp (-t)) * P :=
          mul_le_mul hEexp' (hk.trans hPk) (norm_nonneg _) hE0
      _ = P * Real.exp (|u| * L + D) * Real.exp (-t) := by ring
  · unfold phiH'
    rw [norm_mul, norm_exp]
    have hinner : ‖(-(u : ℂ) + a ^ 2) * (1 / a ^ k) - (k : ℂ) * (1 / a ^ k) * (1 / a)‖ ≤
        P * Real.exp t := by
      calc ‖(-(u : ℂ) + a ^ 2) * (1 / a ^ k) - (k : ℂ) * (1 / a ^ k) * (1 / a)‖
          ≤ ‖(-(u : ℂ) + a ^ 2) * (1 / a ^ k)‖ + ‖(k : ℂ) * (1 / a ^ k) * (1 / a)‖ :=
            norm_sub_le _ _
        _ = ‖-(u : ℂ) + a ^ 2‖ * ‖1 / a ^ k‖ + (k : ℝ) * ‖1 / a ^ k‖ * ‖1 / a‖ := by
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
        _ ≤ ((|u| + 2 * L ^ 2 + 4) * Real.exp t) * (1 / m) ^ k +
              (k : ℝ) * (1 / m) ^ k * (1 / m) := by
            have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
            exact add_le_add (mul_le_mul hpoly hk (norm_nonneg _) (by positivity))
              (mul_le_mul (mul_le_mul_of_nonneg_left hk hk0) h1a (norm_nonneg _) (by positivity))
        _ ≤ P * Real.exp t := by
            have h0 : 0 ≤ (k : ℝ) * (1 / m) ^ k * (1 / m) := by positivity
            have h5 : (k : ℝ) * (1 / m) ^ k * (1 / m) ≤ (k : ℝ) * (1 / m) ^ k * (1 / m) * Real.exp t :=
              le_mul_of_one_le_right h0 het
            have expand : P * Real.exp t = ((|u| + 2 * L ^ 2 + 4) * Real.exp t) * (1 / m) ^ k +
                (k : ℝ) * (1 / m) ^ k * (1 / m) * Real.exp t := by
              rw [hP]; ring
            rw [expand]
            linarith only [h5]
    calc Real.exp ((-(u : ℂ) * a + a ^ 3 / 3).re) *
          ‖(-(u : ℂ) + a ^ 2) * (1 / a ^ k) - (k : ℂ) * (1 / a ^ k) * (1 / a)‖
        ≤ Real.exp ((-(u : ℂ) * a + a ^ 3 / 3).re) * (P * Real.exp t) :=
          mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
      _ = P * (Real.exp ((-(u : ℂ) * a + a ^ 3 / 3).re) * Real.exp t) := by ring
      _ ≤ P * (Real.exp (|u| * L + D) * Real.exp (-t)) := mul_le_mul_of_nonneg_left hEexp hP0
      _ = P * Real.exp (|u| * L + D) * Real.exp (-t) := by ring

/-- K1: `𝓗_∞(u)` does not depend on its negative real vertex. -/
theorem Hinf_vertex_shift (ε : ℝ) (k : ℕ) (u c c' : ℝ) (hc : c < 0) (hc' : c' < 0) :
    SpikedWishart.SoftEdge.Hinf ε k c u = SpikedWishart.SoftEdge.Hinf ε k c' u := by
  unfold SpikedWishart.SoftEdge.Hinf
  congr 1
  have hcos1 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have hsin1 : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hcos2 : Real.cos (-Real.pi / 3) = 1 / 2 := by rw [neg_div, Real.cos_neg]; exact hcos1
  have hsin2 : Real.sin (-Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [neg_div, Real.sin_neg, neg_sq]; exact hsin1
  have hfun : (fun a : ℂ => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k)) = phiH u k := rfl
  rw [hfun]
  refine rayIntegral_vertex_const (phiH u k) (phiH' u k) {z : ℂ | z ≠ 0}
    (fun z hz => phiH_hasDerivAt u k z hz) (phiH'_contOn u k) (Real.pi / 3) (-Real.pi / 3)
    (Iio 0) isOpen_Iio isPreconnected_Iio ?_ hc hc'
  intro s0 hs0
  have hs0' : s0 < 0 := hs0
  obtain ⟨B1, hB1⟩ := phiH_bounds u k (Real.pi / 3) hcos1 hsin1 s0 hs0'
  obtain ⟨B2, hB2⟩ := phiH_bounds u k (-Real.pi / 3) hcos2 hsin2 s0 hs0'
  refine ⟨-s0 / 2, max B1 B2, by linarith only [hs0'], fun s hs t ht => ?_, fun s hs t ht => ?_⟩
  · have hsneg : s < 0 := by linarith [(abs_lt.1 hs).2]
    have g1 := (ray_geom u s t (Real.pi / 3) hcos1 hsin1 hsneg ht).1
    have g2 := (ray_geom u s t (-Real.pi / 3) hcos2 hsin2 hsneg ht).1
    refine ⟨?_, ?_⟩
    · show _ ≠ 0
      intro h0
      rw [h0, norm_zero] at g1
      linarith only [hsneg, g1]
    · show _ ≠ 0
      intro h0
      rw [h0, norm_zero] at g2
      linarith only [hsneg, g2]
  · have he : Real.exp (-t) ≥ 0 := (Real.exp_pos _).le
    have m1 : B1 * Real.exp (-t) ≤ max B1 B2 * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) he
    have m2 : B2 * Real.exp (-t) ≤ max B1 B2 * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) he
    obtain ⟨a1, a2⟩ := hB1 s hs t ht
    obtain ⟨b1, b2⟩ := hB2 s hs t ht
    exact ⟨⟨a1.trans m1, a2.trans m1⟩, ⟨b1.trans m2, b2.trans m2⟩⟩

end P31K1

open Complex MeasureTheory SpikedWishart.SoftEdge in
theorem solution :
    ∀ (ε : ℝ) (k : ℕ) (u c c' : ℝ), c < 0 → c' < 0 → Hinf ε k c u = Hinf ε k c' u := by
  exact P31K1.Hinf_vertex_shift
