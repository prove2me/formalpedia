-- Prove2me | solution 1 for SupplierLearning.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:47:40.682394+00:00
-- url     : https://prove2.me/submissions/85ef8d2e-d572-4d5f-b267-98f776c86601

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_Feasible

open SupplierLearning in
theorem solution (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ)
    (θ : SupplierType) (hq : 0 < (φ θ).q₁) :
    (φ θ).q₂ false ≤ (φ θ).q₂ true := by
  have h1 := hφ.ic_outcome θ true false
  have h2 := hφ.ic_outcome θ false true
  simp only [Params.stagePayoff, Params.learnedCost, outcomeValue] at h1 h2
  have hr : 0 < P.rate θ := by
    cases θ
    · exact hP.rl_pos
    · exact hP.rh_pos
  have hrq := mul_pos hr hq
  nlinarith
