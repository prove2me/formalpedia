-- Prove2me | solution 1 for PI.EF.PK.integral_inv_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:06.139836+00:00
-- url     : https://prove2.me/submissions/97a14e26-118b-45cd-b527-a88c5127d95f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
import Theorems.Thm_PI_EF_PK_continuous_inv_sqrt

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
theorem _root_.solution (T : ℝ) :
    ∫ t in -T..T, 2 * (√(1 + (2 * t) ^ 2))⁻¹ = 2 * Real.arsinh (2 * T) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.arsinh (2 * t)) (2 * (√(1 + (2 * t) ^ 2))⁻¹) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_arsinh (2 * t)).comp t h1
    rw [mul_comm _ (2 : ℝ)] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (continuous_inv_sqrt.intervalIntegrable _ _)]
  simp only [mul_neg, Real.arsinh_neg]
  ring
end PI.EF.PK
