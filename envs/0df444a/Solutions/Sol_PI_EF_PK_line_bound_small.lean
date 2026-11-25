-- Prove2me | solution 1 for PI.EF.PK.line_bound_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:41:02.627912+00:00
-- url     : https://prove2.me/submissions/6e7f196a-91c3-4781-ac94-26f1b14f83ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelB
import Theorems.Thm_PI_EF_PK_norm_log_sub_log_le
import Theorems.Thm_PI_EF_PK_line_ne_zero
import Theorems.Thm_PI_EF_PK_vert_inv_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)‖ ≤ Real.exp (l * c) * (π + |l| * (2 * T)) := by
  have hdec : (fun t : ℝ => ker l ((c : ℂ) + t * I)) = fun t : ℝ =>
      cexp (l * c) * (1 / (((c : ℂ) + t * I) - 0)) +
        cexp (l * c) * ((cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)) := by
    funext t
    have hexp : cexp (l * ((c : ℂ) + t * I)) = cexp (l * c) * cexp (I * ((l * t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    unfold ker
    rw [hexp, sub_zero]
    ring
  have hc1 : Continuous fun t : ℝ => (1 : ℂ) / (((c : ℂ) + t * I) - 0) :=
    continuous_const.div (by fun_prop) (fun t => by simpa using line_ne_zero c hc t)
  have hc2 : Continuous fun t : ℝ => (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I) :=
    Continuous.div (by fun_prop) (by fun_prop) (line_ne_zero c hc)
  rw [hdec, intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
    ((hc2.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← mul_add, norm_mul]
  have hE : ‖cexp (l * c)‖ = Real.exp (l * c) := by
    rw [Complex.norm_exp]; simp
  rw [hE]
  have hP : ‖∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)‖ ≤ π := by
    have h := vert_inv_right (-T) T c 0 (by rw [Complex.zero_re]; exact hc)
    have h2 := norm_log_sub_log_le c T hc
    rw [← h, norm_smul, norm_I, one_mul] at h2
    exact h2
  have hQ : ‖∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖
      ≤ |l| * (2 * T) := by
    have h1 : ∀ t ∈ Set.uIoc (-T) T,
        ‖(cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖ ≤ |l| := by
      intro t _
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (line_ne_zero c hc t))]
      have a1 : ‖cexp (I * ((l * t : ℝ) : ℂ)) - 1‖ ≤ ‖l * t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      have a2 : |t| ≤ ‖(c : ℂ) + t * I‖ := by
        have := Complex.abs_im_le_norm ((c : ℂ) + t * I)
        simpa using this
      calc ‖cexp (I * ((l * t : ℝ) : ℂ)) - 1‖ ≤ ‖l * t‖ := a1
        _ = |l| * |t| := by rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |l| * ‖(c : ℂ) + t * I‖ := by gcongr
    have h2 := norm_integral_le_of_norm_le_const h1
    have e3 : |T - -T| = 2 * T := by
      rw [abs_of_nonneg (by linarith)]; ring
    rwa [e3] at h2
  have hE0 := (Real.exp_pos (l * c)).le
  calc Real.exp (l * c) * ‖(∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)) +
        ∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖
      ≤ Real.exp (l * c) * (‖∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)‖ +
        ‖∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖) := by
        gcongr
        exact norm_add_le _ _
    _ ≤ Real.exp (l * c) * (π + |l| * (2 * T)) := by gcongr
end PI.EF.PK
