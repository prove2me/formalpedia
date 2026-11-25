-- Prove2me | solution 1 for PI.SSU.zero_of_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:11.109412+00:00
-- url     : https://prove2.me/submissions/a495c112-5276-4a64-be50-66cb0ee87e38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_ZeroOfCoef
import Theorems.Thm_PI_SSU_normF_one
import Theorems.Thm_PI_SSU_normF_tau
import Theorems.Thm_PI_SSU_normF_diff

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
theorem _root_.solution (hK : KeyP) (a b A p q : ℂ) (k : ℤ) (ha : a ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hk1 : k = 1 ∨ k = -1)
    (hk : (Real.pi : ℂ) / A * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
      -(2 * (Real.pi : ℂ) * I * k))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (hFa : FE A a p F) (hFb : FE A b q F)
    (h0 : coef (normF a A (Complex.log p) F) 0 = 0) : F = 0 := by
  have hl : Complex.exp (Complex.log p) = p := Complex.exp_log hp
  have hτ : a * (b / a) = b := by field_simp
  have hN := hK (normF a A (Complex.log p) F) (b / a) (q * Complex.exp (cst a b (b / a) A (Complex.log p))) k
    (normF_diff _ _ _ F hF) (mul_ne_zero hq (Complex.exp_ne_zero _)) hk1
    (normF_one a A _ p F hl hFa)
    (fun u => by
      rw [normF_tau a b (b / a) A _ q F hτ hFb u, hk]
      congr 2; ring_nf) h0
  funext z
  have := congrFun hN (z / a)
  simp only [normF, Pi.zero_apply, mul_div_cancel₀ z ha, mul_eq_zero, Complex.exp_ne_zero, or_false]
    at this
  simpa using this
end PI.SSU
