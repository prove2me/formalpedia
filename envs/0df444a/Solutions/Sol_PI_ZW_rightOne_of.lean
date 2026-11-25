-- Prove2me | solution 1 for PI.ZW.rightOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:59.011065+00:00
-- url     : https://prove2.me/submissions/a6520394-1868-489e-88f1-fbabffd869b4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
import Theorems.Thm_PI_ZW_zeta1_eq_sub_one_mul_riemannZeta_of_ne_one
import Theorems.Thm_PI_ZW_zeta1_apply_one
import Theorems.Thm_PI_ZW_order_zeta1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex Filter Topology
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution (hJ : JensenCount) : RightOne := by
  intro hZ hI
  refine ⟨11 / Real.log ((19 / 10) / (37 / 20)), ?_⟩
  intro N _ χ hN t
  subst hN
  have hL : DirichletCharacter.LFunction χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hlogq : 0 < Real.log ((19 / 10 : ℝ) / (37 / 20)) := Real.log_pos (by norm_num)
  set c : ℂ := 2 + (t : ℂ) * Complex.I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have hc1 : c ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hcre] at this
    norm_num at this
  have hAn : AnalyticOnNhd ℂ zeta1 (closedBall c (19 / 10)) := fun z _ =>
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hcre]; norm_num)
  have hfc : zeta1 c ≠ 0 := by
    rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hc1]
    exact mul_ne_zero (sub_ne_zero.2 hc1) hζc
  have hζlow : (1 / 2 : ℝ) ≤ ‖riemannZeta c‖ := by
    have k := hI 1 (1 : DirichletCharacter ℂ 1) c (by rw [hcre]; norm_num)
    rw [DirichletCharacter.LFunction_modOne_eq, hcre] at k
    have hpos : 0 < ‖riemannZeta c‖ := norm_pos_iff.2 hζc
    have k2 : ‖riemannZeta c‖⁻¹ ≤ 2 := by norm_num at k ⊢; linarith
    have := inv_le_of_inv_le₀ hpos k2
    norm_num at this ⊢
    linarith
  have hc1n : (1 : ℝ) ≤ ‖c - 1‖ := by
    have := Complex.abs_re_le_norm (c - 1)
    rw [Complex.sub_re, hcre, Complex.one_re] at this
    norm_num at this
    linarith
  have hfcl : (1 / 2 : ℝ) ≤ ‖zeta1 c‖ := by
    rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hc1, norm_mul]
    nlinarith [norm_nonneg (riemannZeta c)]
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hsph : ∀ z ∈ sphere c (19 / 10), ‖zeta1 z‖ ≤ 13 * (|t| + 5) ^ 2 := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    by_cases hz1 : z = 1
    · rw [hz1, zeta1_apply_one, norm_one]
      nlinarith
    · rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hz1, norm_mul]
      have hre : (1 / 10 : ℝ) ≤ z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, hcre, hz] at this
        have := (abs_le.1 this).1
        linarith
      have hcn : ‖c‖ ≤ 2 + |t| := by
        rw [hc]
        calc ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = 2 + |t| := by simp
      have hzn : ‖z‖ ≤ |t| + 4 := by
        have := norm_le_insert' z c
        have h2 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
          calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
            _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        linarith
      have hz1n : ‖z - 1‖ ≤ |t| + 5 := by
        have := norm_sub_le z 1
        rw [norm_one] at this
        linarith
      have hζ := hZ z (by linarith) hz1
      have hz1pos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
      have hinv : 1 + 1 / z.re ≤ 11 := by
        have : 1 / z.re ≤ 10 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        linarith
      have hA : ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) ≤ (|t| + 5) * (|t| + 5) * 11 := by
        have h1 : 0 ≤ ‖z - 1‖ * ‖z‖ := by positivity
        calc ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) ≤ ‖z - 1‖ * ‖z‖ * 11 := mul_le_mul_of_nonneg_left hinv h1
          _ ≤ (|t| + 5) * (|t| + 5) * 11 := by
            have : ‖z‖ ≤ |t| + 5 := by linarith
            gcongr
      calc ‖z - 1‖ * ‖riemannZeta z‖
          ≤ ‖z - 1‖ * (1 + 1 / ‖z - 1‖ + ‖z‖ * (1 + 1 / z.re)) :=
            mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
        _ = ‖z - 1‖ + ‖z - 1‖ * (1 / ‖z - 1‖) + ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) := by ring
        _ = ‖z - 1‖ + 1 + ‖z - 1‖ * ‖z‖ * (1 + 1 / z.re) := by rw [mul_one_div_cancel hz1pos.ne']
        _ ≤ 13 * (|t| + 5) ^ 2 := by nlinarith
  have hM1 : (1 : ℝ) ≤ 13 * (|t| + 5) ^ 2 := by nlinarith
  have hsub : RightNear χ t ⊆ {z | z ∈ closedBall c (37 / 20) ∧ zeta1 z = 0} := by
    intro ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hρ
    rw [hL] at h4
    have hρ1 : ρ ≠ 1 := by
      intro e
      rw [e] at h2
      simp at h2
    refine ⟨?_, by rw [zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hρ1, h4, mul_zero]⟩
    rw [mem_closedBall, dist_eq_norm]
    have hsq : ‖ρ - c‖ ^ 2 ≤ (37 / 20) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hcre, hcim]
      have := abs_le.1 h3
      nlinarith
    nlinarith [norm_nonneg (ρ - c)]
  obtain ⟨hfin, hsum⟩ := hJ zeta1 c (13 * (|t| + 5) ^ 2) hAn hfc hM1 hsph _ hsub
  refine ⟨hfin, ?_⟩
  rw [hL]
  have hcongr : ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt riemannZeta ρ : ℝ) =
      ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt zeta1 ρ : ℝ) := by
    refine finsum_mem_congr rfl fun ρ hρ => ?_
    have hρ1 : ρ ≠ 1 := by
      intro e
      have h2 := hρ.2.1
      rw [e] at h2
      simp at h2
    rw [order_zeta1 hρ1]
  rw [hcongr]
  refine hsum.trans ?_
  simp only [Nat.cast_one, one_mul]
  set y : ℝ := |t| + 2 with hy
  have hy2 : (2 : ℝ) ≤ y := by linarith
  have hfpos : 0 < ‖zeta1 c‖ := by linarith
  have hq : 13 * (|t| + 5) ^ 2 / ‖zeta1 c‖ ≤ y ^ 11 := by
    rw [div_le_iff₀ hfpos]
    have e1 : |t| + 5 ≤ 3 * y := by linarith
    have e2 : (|t| + 5) ^ 2 ≤ 9 * y ^ 2 := by nlinarith
    have e3 : (256 : ℝ) ≤ y ^ 8 := by
      have := pow_le_pow_left₀ (by norm_num) hy2 8
      norm_num at this
      linarith
    have e4 : y ^ 10 ≤ y ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e5 : 256 * y ^ 2 ≤ y ^ 10 := by
      have := mul_le_mul_of_nonneg_right e3 (sq_nonneg y)
      calc 256 * y ^ 2 ≤ y ^ 8 * y ^ 2 := this
        _ = y ^ 10 := by ring
    have e6 : y ^ 11 * (1 / 2) ≤ y ^ 11 * ‖zeta1 c‖ :=
      mul_le_mul_of_nonneg_left hfcl (by positivity)
    nlinarith
  have hlog : Real.log (13 * (|t| + 5) ^ 2 / ‖zeta1 c‖) ≤ 11 * Real.log y := by
    rw [show (11 : ℝ) * Real.log y = Real.log (y ^ 11) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) hq
  calc Real.log (13 * (|t| + 5) ^ 2 / ‖zeta1 c‖) / Real.log ((19 / 10) / (37 / 20))
      ≤ 11 * Real.log y / Real.log ((19 / 10) / (37 / 20)) := div_le_div_of_nonneg_right hlog hlogq.le
    _ = 11 / Real.log ((19 / 10) / (37 / 20)) * Real.log y := by ring
end PI.ZW
