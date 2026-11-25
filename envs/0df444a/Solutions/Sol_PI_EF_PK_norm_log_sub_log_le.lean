-- Prove2me | solution 1 for PI.EF.PK.norm_log_sub_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:47.849164+00:00
-- url     : https://prove2.me/submissions/630d8a97-aabe-4666-8fde-e9e5127efa99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelB

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
theorem _root_.solution (c T : ℝ) (hc : 0 < c) :
    ‖Complex.log (((c : ℂ) + (T : ℂ) * I) - 0) - Complex.log (((c : ℂ) + ((-T : ℝ) : ℂ) * I) - 0)‖ ≤ π := by
  simp only [sub_zero]
  set z1 : ℂ := (c : ℂ) + T * I with hz1
  set z2 : ℂ := (c : ℂ) + ((-T : ℝ) : ℂ) * I with hz2
  have hconj : (starRingEnd ℂ) z1 = z2 := by
    rw [hz1, hz2, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hn : ‖z1‖ = ‖z2‖ := by rw [← hconj, Complex.norm_conj]
  have hre1 : 0 ≤ z1.re := by simp [hz1]; linarith
  have hre2 : 0 ≤ z2.re := by simp [hz2]; linarith
  have ha1 := Complex.abs_arg_le_pi_div_two_iff.mpr hre1
  have ha2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre2
  calc ‖Complex.log z1 - Complex.log z2‖
      ≤ |(Complex.log z1 - Complex.log z2).re| + |(Complex.log z1 - Complex.log z2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Complex.arg z1 - Complex.arg z2| := by
        rw [Complex.sub_re, Complex.sub_im, Complex.log_re, Complex.log_re, hn, sub_self, abs_zero, zero_add,
          Complex.log_im, Complex.log_im]
    _ ≤ |Complex.arg z1| + |Complex.arg z2| := abs_sub _ _
    _ ≤ π := by linarith
end PI.EF.PK
