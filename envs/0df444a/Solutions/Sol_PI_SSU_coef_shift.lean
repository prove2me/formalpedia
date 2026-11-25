-- Prove2me | solution 1 for PI.SSU.coef_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:04.871091+00:00
-- url     : https://prove2.me/submissions/cea65cb5-3cdf-4409-acce-400fdcd96f57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_CoefShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SSU
open Complex
namespace PI.SSU
theorem _root_.solution (hS : ShiftInv) (f : ℂ → ℂ) (τ K : ℂ) (k : ℤ) (hf : Differentiable ℂ f)
    (h1 : ∀ u, f (u + 1) = f u)
    (hτ : ∀ u, f (u + τ) = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * k * u)) * f u) (n : ℤ) :
    coef f n = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * τ)) * coef f (n + k) := by
  rw [← hS f hf h1 τ n, ← hS f hf h1 0 (n + k), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [hτ, add_zero]
  have e : cexp (-(2 * (Real.pi : ℂ) * I * k * x)) * cexp (-(2 * (Real.pi : ℂ) * I * n * (x + τ))) =
      cexp (-(2 * (Real.pi : ℂ) * I * n * τ)) * cexp (-(2 * (Real.pi : ℂ) * I * ((n + k : ℤ) : ℂ) * x)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (K * f x) * e
end PI.SSU
