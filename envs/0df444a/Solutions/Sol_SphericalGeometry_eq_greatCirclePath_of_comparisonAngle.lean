-- Prove2me | solution 1 for SphericalGeometry.eq_greatCirclePath_of_comparisonAngle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T06:51:07.922598+00:00
-- url     : https://prove2.me/submissions/7abd3876-4d56-4d10-94c4-ed1037f4dc64

import Definitions.Def_spherical_great_circle
import Definitions.Def_metric_geodesic_angle
import Theorems.Thm_SphericalGeometry_eq_greatCirclePath_of_inner_eq_cos

open SphericalGeometry MetricGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gamma : ℝ → E) (L alpha delta : ℝ) (hL : 0 < L) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hsmall : alpha * delta < Real.pi)
    (hsphere : ∀ theta : ℝ, ‖gamma theta‖ = L)
    (hangle : ∀ theta1 theta2 : ℝ, |theta1 - theta2| ≤ delta →
      comparisonAngle 0 (gamma theta1) (gamma theta2) = alpha * |theta1 - theta2|)
    (theta0 : ℝ) :
    ∃ v1 v2 : E, ‖v1‖ = 1 ∧ ‖v2‖ = 1 ∧ inner ℝ v1 v2 = 0 ∧
      ∀ theta : ℝ, |theta - theta0| ≤ delta / 2 →
        gamma theta = L • greatCirclePath v1 v2 (alpha * (theta - theta0)) := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have halpha0 : alpha ≠ 0 := ne_of_gt halpha
  -- the cosine of the comparison angle at the origin is the normalised inner product
  have hcos : ∀ x y : E, ‖x‖ = L → ‖y‖ = L →
      Real.cos (comparisonAngle 0 x y) = inner ℝ x y / L ^ 2 := by
    intro x y hx hy
    have hxy : dist x y ^ 2 = 2 * L ^ 2 - 2 * inner ℝ x y := by
      rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_sub_self,
        real_inner_comm y x]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx, hy]
      ring
    have hd0x : dist 0 x = L := by rw [dist_zero_left, hx]
    have hd0y : dist 0 y = L := by rw [dist_zero_left, hy]
    have harg : (dist 0 x ^ 2 + dist 0 y ^ 2 - dist x y ^ 2)
        / (2 * dist 0 x * dist 0 y) = inner ℝ x y / L ^ 2 := by
      rw [hd0x, hd0y, hxy]
      field_simp
      ring
    have hle : |(inner ℝ x y : ℝ)| ≤ L ^ 2 := by
      have := abs_real_inner_le_norm x y
      rw [hx, hy] at this
      nlinarith [this]
    have hb1 : (-1 : ℝ) ≤ inner ℝ x y / L ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have := abs_le.mp hle
      linarith [this.1]
    have hb2 : (inner ℝ x y : ℝ) / L ^ 2 ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      have := abs_le.mp hle
      linarith [this.2]
    unfold comparisonAngle
    rw [harg, Real.cos_arccos hb1 hb2]
  -- the rescaled and reparametrised curve is unit speed on the sphere
  set eta : ℝ → E := fun s => L⁻¹ • gamma (theta0 + s / alpha) with hetadef
  have hetanorm : ∀ s : ℝ, ‖eta s‖ = 1 := by
    intro s
    rw [hetadef]
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hL, hsphere]
    field_simp
  have hetainner : ∀ s t : ℝ, |s - t| ≤ alpha * delta →
      inner ℝ (eta s) (eta t) = Real.cos (s - t) := by
    intro s t hst
    have hpar : |(theta0 + s / alpha) - (theta0 + t / alpha)| ≤ delta := by
      have h1 : (theta0 + s / alpha) - (theta0 + t / alpha) = (s - t) / alpha := by
        field_simp
        ring
      rw [h1, abs_div, abs_of_pos halpha, div_le_iff₀ halpha]
      linarith [hst, mul_comm alpha delta]
    have hang := hangle (theta0 + s / alpha) (theta0 + t / alpha) hpar
    have hc := hcos (gamma (theta0 + s / alpha)) (gamma (theta0 + t / alpha))
      (hsphere _) (hsphere _)
    rw [hang] at hc
    have hval : alpha * |(theta0 + s / alpha) - (theta0 + t / alpha)| = |s - t| := by
      have h1 : (theta0 + s / alpha) - (theta0 + t / alpha) = (s - t) / alpha := by
        field_simp
        ring
      rw [h1, abs_div, abs_of_pos halpha]
      field_simp
    rw [hval] at hc
    have hinnerval : inner ℝ (gamma (theta0 + s / alpha)) (gamma (theta0 + t / alpha))
        = L ^ 2 * Real.cos (s - t) := by
      rw [← Real.cos_abs (s - t), hc]
      field_simp
    rw [hetadef]
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [hinnerval]
    field_simp
  obtain ⟨v1, v2, hv1, hv2, hv12, hkey⟩ :=
    SphericalGeometry.eq_greatCirclePath_of_inner_eq_cos eta (alpha * delta)
      (by positivity) hsmall hetanorm hetainner 0
  refine ⟨v1, v2, hv1, hv2, hv12, ?_⟩
  intro theta htheta
  have hs : |alpha * (theta - theta0) - 0| ≤ alpha * delta / 2 := by
    rw [sub_zero, abs_mul, abs_of_pos halpha]
    have : |theta - theta0| ≤ delta / 2 := htheta
    nlinarith [this, halpha]
  have := hkey (alpha * (theta - theta0)) hs
  rw [hetadef] at this
  simp only [sub_zero] at this
  have harg : theta0 + alpha * (theta - theta0) / alpha = theta := by
    field_simp
    ring
  rw [harg] at this
  rw [← this, smul_smul, mul_inv_cancel₀ hL0, one_smul]
