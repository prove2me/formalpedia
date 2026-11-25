-- Prove2me | solution 1 for PI.SSU.normF_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:10.353976+00:00
-- url     : https://prove2.me/submissions/8e0a31e9-80b6-48a0-810d-1d1e338e8d17

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
theorem _root_.solution (a A l p : ℂ) (F : ℂ → ℂ) (hl : Complex.exp l = p) (hF : FE A a p F) (u : ℂ) :
    normF a A l F (u + 1) = normF a A l F u := by
  unfold normF
  have h1 := hF (a * u)
  have e1 : a * (u + 1) = a * u + a := by ring
  rw [e1]
  have hF' : F (a * u + a) = p * F (a * u) * Complex.exp (-(-(Real.pi : ℂ) * (a * u) * (starRingEnd ℂ) a / A -
      (Real.pi : ℂ) * a * (starRingEnd ℂ) a / (2 * A))) := by
    rw [← h1, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hF', ← hl]
  have key : ∀ (P e1 e2 e3 e4 : ℂ), e1 + e2 + e3 = e4 →
      Complex.exp e1 * P * Complex.exp e2 * Complex.exp e3 = P * Complex.exp e4 := by
    intro P e1 e2 e3 e4 h
    rw [← h, Complex.exp_add, Complex.exp_add]
    ring
  apply key
  ring
end PI.SSU
