-- Prove2me | solution 1 for PI.SSU.normF_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:16.030497+00:00
-- url     : https://prove2.me/submissions/4e6d52ff-9282-49fe-bd05-3753f9ec3727

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
theorem _root_.solution (a b τ A l q : ℂ) (F : ℂ → ℂ) (hτ : a * τ = b) (hF : FE A b q F) (u : ℂ) :
    normF a A l F (u + τ) = (q * Complex.exp (cst a b τ A l)) *
      Complex.exp ((Real.pi : ℂ) / A * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) * u) *
      normF a A l F u := by
  unfold normF
  subst hτ
  have h1 := hF (a * u)
  have e1 : a * (u + τ) = a * u + a * τ := by ring
  rw [e1]
  have hF' : F (a * u + a * τ) = q * F (a * u) * Complex.exp (-(-(Real.pi : ℂ) * (a * u) *
      (starRingEnd ℂ) (a * τ) / A - (Real.pi : ℂ) * (a * τ) * (starRingEnd ℂ) (a * τ) / (2 * A))) := by
    rw [← h1, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hF']
  unfold cst
  have key : ∀ (qq P e1 e2 e3 e4 e5 : ℂ), e1 + e2 = e3 + e4 + e5 →
      qq * P * Complex.exp e1 * Complex.exp e2 = qq * Complex.exp e3 * Complex.exp e4 * (P * Complex.exp e5) := by
    intro qq P e1 e2 e3 e4 e5 h
    have h2 : Complex.exp e1 * Complex.exp e2 = Complex.exp e3 * Complex.exp e4 * Complex.exp e5 := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination (qq * P) * h2
  apply key
  simp only [map_mul]
  ring
end PI.SSU
