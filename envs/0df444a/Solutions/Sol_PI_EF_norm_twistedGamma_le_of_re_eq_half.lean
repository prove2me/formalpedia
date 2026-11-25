-- Prove2me | solution 1 for PI.EF.norm_twistedGamma_le_of_re_eq_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:22.490494+00:00
-- url     : https://prove2.me/submissions/9f17c1d9-9d11-4e91-9fbc-81ec781b9d98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Theorems.Thm_PI_EF_half_line
import Theorems.Thm_PI_EF_norm_twistedGamma
import Theorems.Thm_PI_EF_one_le_norm_add_one
import Theorems.Thm_PI_EF_eq_re_add_im

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
theorem _root_.solution (w : ℂ) (hw : w.re = 1 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  rw [norm_twistedGamma]
  have h1 := one_le_norm_add_one (w := w) (by rw [hw]; norm_num)
  have e : w = 1 / 2 + (w.im : ℂ) * I := by
    conv_lhs => rw [eq_re_add_im w, hw]
    push_cast
    ring
  have h2 := half_line w.im
  rw [← e] at h2
  have h3 : Real.exp (Real.pi / 2 * w.im) ≤ Real.exp (Real.pi / 2 * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  have h4 : (1 : ℝ) ≤ ‖w + 1‖ ^ 5 := one_le_pow₀ h1
  rw [div_le_iff₀ (by linarith)]
  have h5 : ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im) ≤ 3 :=
    (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
  nlinarith
end PI.EF
