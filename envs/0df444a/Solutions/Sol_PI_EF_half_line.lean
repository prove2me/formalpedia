-- Prove2me | solution 1 for PI.EF.half_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:27.816261+00:00
-- url     : https://prove2.me/submissions/262b6a1a-37b6-4d58-ae17-638a10ab958d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Theorems.Thm_PI_EF_norm_sq_Gamma_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Set
namespace PI.EF
theorem _root_.solution (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|) ≤ 3 := by
  have h := norm_sq_Gamma_half t
  have hpi := Real.pi_pos
  have hc : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos hpi, Real.cosh_eq]
    have := Real.exp_pos (-(Real.pi * |t|))
    linarith
  have he : Real.exp (Real.pi / 2 * |t|) ^ 2 = Real.exp (Real.pi * |t|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hE := Real.exp_pos (Real.pi * |t|)
  have hsq : (‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|)) ^ 2 ≤ 9 := by
    rw [mul_pow, h, he, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have := Real.pi_lt_four
    nlinarith
  have h0 : 0 ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|) := by positivity
  by_contra hcon
  rw [not_le] at hcon
  nlinarith
end PI.EF
