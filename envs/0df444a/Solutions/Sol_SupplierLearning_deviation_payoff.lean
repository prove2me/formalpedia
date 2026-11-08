-- Prove2me | solution 1 for SupplierLearning.deviation_payoff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:44:49.212394+00:00
-- url     : https://prove2.me/submissions/975b636b-ebd9-4aa5-973a-bad35f08d1d9

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_Feasible

open SupplierLearning in
theorem solution (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ)
    (hq : 0 < (φ .h).q₁) :
    P.supplierPayoff φ .l .h =
      (φ .h).p₁ - P.cl * (φ .h).q₁ +
        P.δ * P.ρ * ((φ .h).p₂ true - (P.cl - P.rl * (φ .h).q₁) * (φ .h).q₂ true) +
        P.δ * (1 - P.ρ) *
          max ((φ .h).p₂ true - P.cl * (φ .h).q₂ true) ((φ .h).p₂ false - P.cl * (φ .h).q₂ false) := by
  have hA := hφ.ic_outcome .h true false
  have hB := hφ.ic_outcome .h false true
  have cap := hφ.capacity .h
  simp only [Params.stagePayoff, Params.learnedCost, Params.cost, Params.rate, outcomeValue,
    mul_one, mul_zero, sub_zero] at hA hB
  have hΔ : (φ .h).q₂ false ≤ (φ .h).q₂ true := by
    by_contra hc
    push_neg at hc
    have := mul_pos (mul_pos hP.rh_pos hq) (sub_pos.mpr hc)
    nlinarith
  have key : P.stagePayoff .l true (φ .h) false ≤ P.stagePayoff .l true (φ .h) true := by
    simp only [Params.stagePayoff, Params.learnedCost, Params.cost, Params.rate, outcomeValue,
      mul_one]
    nlinarith [mul_nonneg (show 0 ≤ (P.ch - P.rh * (φ .h).q₁) - (P.cl - P.rl * (φ .h).q₁) by
      linarith) (sub_nonneg.mpr hΔ)]
  simp only [Params.supplierPayoff, Params.expectOutcome]
  rw [max_eq_right key]
  simp only [Params.stagePayoff, Params.learnedCost, Params.cost, Params.rate, outcomeValue,
    mul_one, mul_zero, sub_zero]
  rw [max_comm]
  ring
