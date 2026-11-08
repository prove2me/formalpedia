-- Prove2me | solution 1 for SupplierLearning.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:32:37.026103+00:00
-- url     : https://prove2.me/submissions/a448630c-ab5f-41eb-9082-6ac4db38ef2b

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_stagePayoff
import Definitions.Def_SupplierLearning_Params_Feasible

open SupplierLearning in
theorem solution (P : SupplierLearning.Params) (hP : P.Standing) {φ : SupplierLearning.Contract}
    (hφ : P.Feasible φ) (hq : 0 < (φ .h).q₁) :
    P.stagePayoff .l true (φ .h) false ≤ P.stagePayoff .l true (φ .h) true := by
  have h1 := hφ.ic_outcome .h true false
  have h2 := hφ.ic_outcome .h false true
  have hc := hφ.capacity .h
  simp only [SupplierLearning.Params.stagePayoff, SupplierLearning.Params.learnedCost,
    SupplierLearning.Params.cost, SupplierLearning.Params.rate,
    SupplierLearning.outcomeValue] at h1 h2 ⊢
  have hrq : 0 < P.rh * (φ .h).q₁ := mul_pos hP.rh_pos hq
  have hmono : (φ .h).q₂ false ≤ (φ .h).q₂ true := by
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_pos hrq (sub_pos.2 hlt)]
  nlinarith [mul_nonneg (sub_nonneg.2 hmono)
    (by linarith : (0:ℝ) ≤ (P.ch - P.rh * (φ .h).q₁) - (P.cl - P.rl * (φ .h).q₁))]
