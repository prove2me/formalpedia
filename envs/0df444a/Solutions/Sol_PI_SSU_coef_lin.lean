-- Prove2me | solution 1 for PI.SSU.coef_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:16:59.461666+00:00
-- url     : https://prove2.me/submissions/3dd8e6ae-49ad-4eb2-bc57-356403fba16f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_ZeroOfCoef

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
theorem _root_.solution (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g) (α β : ℂ) (n : ℤ) :
    coef (fun u => α * f u - β * g u) n = α * coef f n - β * coef g n := by
  unfold coef
  have hf' : IntervalIntegrable (fun x : ℝ => f x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg' : IntervalIntegrable (fun x : ℝ => g x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hf'.const_mul α) (hg'.const_mul β)]
  congr 1
  funext x
  ring
end PI.SSU
