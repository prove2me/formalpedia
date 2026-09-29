-- Prove2me | solution 1 for SphericalGeometry.eq_greatCirclePath_of_inner_eq_cos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T06:49:44.301742+00:00
-- url     : https://prove2.me/submissions/ef356e1b-d6f0-45a5-8757-3c0892b77351

import Definitions.Def_spherical_great_circle

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gamma : ℝ → E) (delta : ℝ) (hdelta : 0 < delta) (hdpi : delta < Real.pi)
    (hnorm : ∀ s : ℝ, ‖gamma s‖ = 1)
    (hinner : ∀ s t : ℝ, |s - t| ≤ delta →
      inner ℝ (gamma s) (gamma t) = Real.cos (s - t))
    (s0 : ℝ) :
    ∃ v1 v2 : E, ‖v1‖ = 1 ∧ ‖v2‖ = 1 ∧ inner ℝ v1 v2 = 0 ∧
      ∀ s : ℝ, |s - s0| ≤ delta / 2 →
        gamma s = greatCirclePath v1 v2 (s - s0) := by
  set t0 : ℝ := delta / 2 with ht0def
  have ht0 : 0 < t0 := by positivity
  have ht0pi : t0 < Real.pi := by
    have : delta / 2 < delta := by linarith
    linarith
  have hsinpos : 0 < Real.sin t0 := Real.sin_pos_of_pos_of_lt_pi ht0 ht0pi
  have hsin : Real.sin t0 ≠ 0 := ne_of_gt hsinpos
  set a : E := gamma s0 with hadef
  set c : E := gamma (s0 + t0) with hcdef
  have hna : ‖a‖ = 1 := hnorm s0
  have hnc : ‖c‖ = 1 := hnorm (s0 + t0)
  have hac : inner ℝ a c = Real.cos t0 := by
    have h := hinner s0 (s0 + t0) (by
      rw [show s0 - (s0 + t0) = -t0 by ring, abs_neg, abs_of_pos ht0]
      linarith)
    rw [show s0 - (s0 + t0) = -t0 by ring, Real.cos_neg] at h
    exact h
  set b : E := (Real.sin t0)⁻¹ • (c - Real.cos t0 • a) with hbdef
  have hcb : c = Real.cos t0 • a + Real.sin t0 • b := by
    rw [hbdef, smul_smul, mul_inv_cancel₀ hsin, one_smul]
    abel
  have hab : inner ℝ a b = (0 : ℝ) := by
    rw [hbdef, real_inner_smul_right, inner_sub_right, real_inner_smul_right, hac,
      real_inner_self_eq_norm_sq, hna]
    ring
  have hnum : ‖c - Real.cos t0 • a‖ ^ 2 = Real.sin t0 ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm a c, hac, norm_smul,
      Real.norm_eq_abs, hna, hnc, mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq t0]
  have hbn : ‖b‖ = 1 := by
    have h1 : ‖c - Real.cos t0 • a‖ = Real.sin t0 := by
      nlinarith [hnum, norm_nonneg (c - Real.cos t0 • a), hsinpos]
    rw [hbdef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsinpos, h1,
      inv_mul_cancel₀ hsin]
  refine ⟨a, b, hna, hbn, hab, ?_⟩
  intro s hs
  have habs1 : |s - s0| ≤ delta := by
    have : delta / 2 ≤ delta := by linarith
    linarith [hs, this]
  have habs2 : |s - (s0 + t0)| ≤ delta := by
    have h1 : s - (s0 + t0) = (s - s0) - t0 := by ring
    rw [h1]
    have := abs_sub (s - s0) t0
    have h2 : |(s - s0) - t0| ≤ |s - s0| + |t0| := abs_sub _ _
    rw [abs_of_pos ht0] at h2
    have : |s - s0| ≤ delta / 2 := hs
    linarith
  have h1 : inner ℝ (gamma s) a = Real.cos (s - s0) := hinner s s0 habs1
  have h2 : inner ℝ (gamma s) c = Real.cos (s - s0 - t0) := by
    have := hinner s (s0 + t0) habs2
    rwa [show s - (s0 + t0) = s - s0 - t0 by ring] at this
  have h3 : inner ℝ (gamma s) b = Real.sin (s - s0) := by
    have hexp : inner ℝ (gamma s) c
        = Real.cos t0 * Real.cos (s - s0)
          + Real.sin t0 * inner ℝ (gamma s) b := by
      rw [hcb, inner_add_right, real_inner_smul_right, real_inner_smul_right, h1]
    have hcos : Real.cos (s - s0 - t0)
        = Real.cos (s - s0) * Real.cos t0 + Real.sin (s - s0) * Real.sin t0 :=
      Real.cos_sub (s - s0) t0
    rw [h2, hcos] at hexp
    have hmul : Real.sin t0 * Real.sin (s - s0)
        = Real.sin t0 * inner ℝ (gamma s) b := by linear_combination hexp
    exact (mul_left_cancel₀ hsin hmul).symm
  have hP : ‖gamma s - greatCirclePath a b (s - s0)‖ ^ 2 = 0 := by
    have hPn : ‖greatCirclePath a b (s - s0)‖ ^ 2 = 1 := by
      rw [greatCirclePath, ← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hna, hbn,
        real_inner_comm a b, hab]
      nlinarith [Real.sin_sq_add_cos_sq (s - s0)]
    have hPi : inner ℝ (gamma s) (greatCirclePath a b (s - s0)) = (1 : ℝ) := by
      rw [greatCirclePath]
      simp only [inner_add_right, real_inner_smul_right]
      rw [h1, h3]
      nlinarith [Real.sin_sq_add_cos_sq (s - s0)]
    rw [norm_sub_sq_real, hPn, hPi]
    have := hnorm s
    nlinarith [this]
  have : gamma s - greatCirclePath a b (s - s0) = 0 := by
    have hz : ‖gamma s - greatCirclePath a b (s - s0)‖ = 0 := by nlinarith [hP, norm_nonneg (gamma s - greatCirclePath a b (s - s0))]
    exact norm_eq_zero.mp hz
  exact sub_eq_zero.mp this
