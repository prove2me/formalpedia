-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_log_normSq_add_exp_e27e3649b0c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:43.474774+00:00
-- url     : https://prove2.me/submissions/eedc2324-18e9-428c-b963-2c0a8552659a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_comp_real_2280461a8adc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_comp_real_4d15d05546d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_sq_norm_eq_re_im_995b20f7781c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_normSq_analytic_f5d0991fe1ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_normSq_analytic_a0251b8db114
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {S : (ι → ℂ) → ℂ} {Φ : (ι → ℂ) → ℝ} {y : ι → ℂ} {ε : ℝ}
    (hS : AnalyticAt ℂ S y) (hΦ : ContDiffAt ℝ 2 Φ y) (hε : 0 < ε) (w : ι → ℂ) :
    2 * (ε * Real.exp (2 * Φ y)) / (‖S y‖ ^ 2 + ε * Real.exp (2 * Φ y)) * levi Φ y w ≤
      levi (fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z))) y w := by
  set h : (ι → ℂ) → ℝ := fun z => ‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z) with hh
  have hpos : ∀ z, 0 < h z := fun z => by
    have := Real.exp_pos (2 * Φ z)
    positivity
  have hSc : ContDiffAt ℝ 2 S y := (hS.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hQ : ContDiffAt ℝ 2 (fun z => ‖S z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt.comp y hSc
  have h2Φ : ContDiffAt ℝ 2 (fun z => 2 * Φ z) y := contDiffAt_const.mul hΦ
  have hE : ContDiffAt ℝ 2 (fun z => Real.exp (2 * Φ z)) y := h2Φ.exp
  have hhc : ContDiffAt ℝ 2 h y := hQ.add (contDiffAt_const.mul hE)
  have l2Φ := levi_comp_real (G := fun x : ℝ => 2 * x) (G₁ := fun _ => 2) (g₂ := 0) hΦ
    (Eventually.of_forall fun z => by simpa using (hasDerivAt_id (Φ z)).const_mul (2 : ℝ))
    (hasDerivAt_const _ _) w
  have lE := levi_comp_real (G := Real.exp) (G₁ := Real.exp) (g₂ := Real.exp (2 * Φ y)) h2Φ
    (Eventually.of_forall fun z => Real.hasDerivAt_exp _) (Real.hasDerivAt_exp _) w
  have d2Φ : ∀ v, fderiv ℝ (fun z => 2 * Φ z) y v = 2 * fderiv ℝ Φ y v := fun v =>
    fderiv_comp_real (G := fun x : ℝ => 2 * x) (hΦ.differentiableAt (by norm_num))
      (by simpa using (hasDerivAt_id (Φ y)).const_mul (2 : ℝ)) v
  have dE : ∀ v, fderiv ℝ (fun z => Real.exp (2 * Φ z)) y v =
      Real.exp (2 * Φ y) * (2 * fderiv ℝ Φ y v) := fun v => by
    rw [fderiv_comp_real (G := Real.exp) (h2Φ.differentiableAt (by norm_num))
      (Real.hasDerivAt_exp _), d2Φ]
  have dh : ∀ v, fderiv ℝ h y v = 2 * ((S y).re * (fderiv ℂ S y v).re +
      (S y).im * (fderiv ℂ S y v).im) + ε * (Real.exp (2 * Φ y) * (2 * fderiv ℝ Φ y v)) := by
    intro v
    have d1 : DifferentiableAt ℝ (fun z => ‖S z‖ ^ 2) y := hQ.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ (fun z => ε * Real.exp (2 * Φ z)) y :=
      (contDiffAt_const.mul hE).differentiableAt (by norm_num)
    rw [hh, fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply, fderiv_normSq_analytic hS,
      fderiv_const_mul (hE.differentiableAt (by norm_num)), ContinuousLinearMap.smul_apply,
      dE, smul_eq_mul]
  have lh : levi h y w = ‖fderiv ℂ S y w‖ ^ 2 + ε * (Real.exp (2 * Φ y) * (2 * levi Φ y w) +
      Real.exp (2 * Φ y) * ((2 * fderiv ℝ Φ y w) ^ 2 +
        (2 * fderiv ℝ Φ y (Complex.I • w)) ^ 2) / 4) := by
    rw [hh, levi_add_smul ε hQ hE, levi_normSq_analytic hS, lE, l2Φ, d2Φ, d2Φ]
    ring
  have lK := levi_comp_real (G := Real.log) (G₁ := fun x => x⁻¹) (g₂ := -(h y ^ 2)⁻¹) hhc
    (Eventually.of_forall fun z => Real.hasDerivAt_log (hpos z).ne')
    (hasDerivAt_inv (hpos y).ne') w
  change _ ≤ levi (fun z => Real.log (h z)) y w
  rw [lK, lh, dh, dh, (fderiv ℂ S y).map_smul Complex.I w, sq_norm_eq_re_im (fderiv ℂ S y w)]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  set E := ε * Real.exp (2 * Φ y) with hEdef
  have hEpos : 0 < E := mul_pos hε (Real.exp_pos _)
  have hy : h y = ‖S y‖ ^ 2 + E := rfl
  rw [sq_norm_eq_re_im (S y)] at hy
  set σr := (S y).re
  set σi := (S y).im
  set ar := (fderiv ℂ S y w).re
  set ai := (fderiv ℂ S y w).im
  set b₁ := fderiv ℝ Φ y w
  set b₂ := fderiv ℝ Φ y (Complex.I • w)
  set L := levi Φ y w
  have hhy : 0 < h y := hpos y
  rw [show ‖S y‖ ^ 2 + E = h y from rfl]
  have key : (h y)⁻¹ * (ar ^ 2 + 1 * ai ^ 2 + ε * (Real.exp (2 * Φ y) * (2 * L) +
      Real.exp (2 * Φ y) * ((2 * b₁) ^ 2 + (2 * b₂) ^ 2) / 4)) +
      -(h y ^ 2)⁻¹ * ((2 * (σr * ar + σi * ai) + ε * (Real.exp (2 * Φ y) * (2 * b₁))) ^ 2 +
        (2 * (σr * (0 * ar - 1 * ai) + σi * (0 * ai + 1 * ar)) +
          ε * (Real.exp (2 * Φ y) * (2 * b₂))) ^ 2) / 4 - 2 * E / h y * L =
      E * ((ar - (σr * b₁ + σi * b₂)) ^ 2 + (ai - (σi * b₁ - σr * b₂)) ^ 2) / h y ^ 2 := by
    rw [hy]
    field_simp
    rw [hEdef]
    ring
  have hnn : 0 ≤ E * ((ar - (σr * b₁ + σi * b₂)) ^ 2 + (ai - (σi * b₁ - σr * b₂)) ^ 2) / h y ^ 2 :=
    by positivity
  linarith
end GroundTheory.Heights₂.Heights.AnalyticLimit
