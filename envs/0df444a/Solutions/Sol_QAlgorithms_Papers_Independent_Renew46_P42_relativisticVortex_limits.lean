-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.relativisticVortex_limits
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:00:48.672873+00:00
-- url     : https://prove2.me/submissions/c433ff2e-bdb6-4453-a30f-48e9812abf65

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)


/-- PDF p.8, (72)–(74): limits are taken strictly outside the singular core. -/
theorem solution (c W rho : ℝ)
    (hc : 0 < c) (hW : 0 < W) (hrho : 0 < rho) :
    Tendsto (vortexPressure c W rho) (nhdsWithin 0 (Ioi 0)) (nhds (-rho * c ^ 2)) ∧
    Tendsto (vortexSpeed c W) (nhdsWithin 0 (Ioi 0)) (nhds c) ∧
    Tendsto (fun r => r ^ 2 * vortexPressure c W rho r) atTop (nhds (-rho * W ^ 2 / 2)) ∧
    Tendsto (fun r => r * vortexSpeed c W r) atTop (nhds W) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hγcont : Continuous (fun r : ℝ => Real.sqrt (r ^ 2 + W ^ 2 / c ^ 2)) := by fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- pressure at 0+
    have h1 : Tendsto (fun r : ℝ => r ^ 2) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun r : ℝ => r ^ 2) (nhds 0) (nhds (0 ^ 2)) := (continuous_pow 2).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact pow_pos (show (0:ℝ) < r from hr) 2
    have h2 := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (show 0 < W ^ 2 / (2 * c ^ 2) by positivity)
    have h3 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)
    have h4 := (h3.const_mul (rho * c ^ 2)).sub_const (rho * c ^ 2)
    simp only [mul_zero, zero_sub] at h4
    rw [show -(rho * c ^ 2) = -rho * c ^ 2 by ring] at h4
    convert h4 using 2 with r
    simp only [vortexPressure, Function.comp]
    congr 2
    field_simp
  · -- speed at 0+
    have heq : ∀ r : ℝ, 0 < r → vortexSpeed c W r = W / Real.sqrt (r ^ 2 + W ^ 2 / c ^ 2) := by
      intro r hr
      rw [vortexSpeed, vortexGamma]
      congr 1
      rw [show r ^ 2 + W ^ 2 / c ^ 2 = (1 + W ^ 2 / (c ^ 2 * r ^ 2)) * r ^ 2 by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
    have hlim : Tendsto (fun r : ℝ => W / Real.sqrt (r ^ 2 + W ^ 2 / c ^ 2)) (nhds 0)
        (nhds (W / Real.sqrt (0 ^ 2 + W ^ 2 / c ^ 2))) := by
      apply Tendsto.div tendsto_const_nhds (hγcont.tendsto 0)
      positivity
    have hv : W / Real.sqrt (0 ^ 2 + W ^ 2 / c ^ 2) = c := by
      rw [show (0:ℝ) ^ 2 + W ^ 2 / c ^ 2 = (W / c) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      field_simp
    rw [hv] at hlim
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (heq r hr).symm
  · -- r^2 P
    set a := W ^ 2 / (2 * c ^ 2)
    have hd : HasDerivAt (fun t : ℝ => rho * c ^ 2 * Real.exp (-a * t) - rho * c ^ 2)
        (rho * c ^ 2 * (Real.exp (-a * 0) * (-a))) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).const_mul (-a)).exp
      simpa using (this.const_mul (rho * c ^ 2)).sub_const (rho * c ^ 2)
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have hinv : Tendsto (fun r : ℝ => (r ^ 2)⁻¹) atTop (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).inv_tendsto_atTop
      · filter_upwards [eventually_gt_atTop 0] with r hr
        simp only [mem_compl_iff, mem_singleton_iff, inv_eq_zero]; positivity
    have := hd.comp hinv
    have hval : rho * c ^ 2 * (Real.exp (-a * 0) * (-a)) = -rho * W ^ 2 / 2 := by
      simp [a]; field_simp
    rw [hval] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    simp only [Function.comp, smul_eq_mul, zero_add, mul_zero, Real.exp_zero, mul_one, sub_self,
      sub_zero, inv_inv, vortexPressure]
    congr 3
    simp only [a]; field_simp
  · -- r * speed
    have hg : Tendsto (fun r : ℝ => vortexGamma c W r) atTop (nhds 1) := by
      have h0 : Tendsto (fun r : ℝ => W ^ 2 / (c ^ 2 * r ^ 2)) atTop (nhds 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).const_mul_atTop hc2
      have := ((h0.const_add 1).sqrt)
      simpa [vortexGamma] using this
    have := (tendsto_const_nhds (x := W)).div hg one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    simp only [Pi.div_apply, vortexSpeed]; field_simp


end

