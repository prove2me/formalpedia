-- Prove2me | solution 1 for PI.IsoInvMetricW.poly_eq_zero_of_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:38.115861+00:00
-- url     : https://prove2.me/submissions/445f1d40-7178-44b0-b720-d85e0df2cd08

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
open PI PI.IsoInvMetricW
namespace PI.IsoInvMetricW
theorem _root_.solution (P : ℂ[X]) (h : ∀ z : ℂ, ‖z‖ = 1 → P.eval z = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Set.InjOn (fun t : ℝ => Complex.exp (t * Complex.I)) (Set.Ioo 0 1) := by
    intro a ha b hb hab
    have hpi := Real.pi_gt_three
    have := Complex.exp_inj_of_neg_pi_lt_of_le_pi ?_ ?_ ?_ ?_ hab
    · simpa using this
    all_goals simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, zero_mul, add_zero]
    all_goals linarith [ha.1, ha.2, hb.1, hb.2]
  refine ((Set.Ioo_infinite (by norm_num : (0:ℝ) < 1)).image hinj).mono ?_
  rintro _ ⟨t, -, rfl⟩
  exact h _ (Complex.norm_exp_ofReal_mul_I t)
end PI.IsoInvMetricW
