-- Prove2me | solution 1 for SupplierLearning.claim_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:41:56.350039+00:00
-- url     : https://prove2.me/submissions/ef2e13ad-5644-4732-9c47-7e1332520e36

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Term
import Definitions.Def_SupplierLearning_Params_stagePayoff

open SupplierLearning in
theorem solution (P : Params) (t : Term)
    (hbind : P.stagePayoff .h true t true = P.stagePayoff .h true t false)
    (hx : t.q₂ false ≤ t.q₂ true) :
    (P.ch - P.rh * t.q₁ ≤ P.cl → P.stagePayoff .l false t true ≤ P.stagePayoff .l false t false) ∧
    (P.cl < P.ch - P.rh * t.q₁ →
      P.stagePayoff .l false t false ≤ P.stagePayoff .l false t true ∧
        (t.q₂ false < t.q₂ true → P.stagePayoff .l false t false < P.stagePayoff .l false t true)) := by
  simp only [Params.stagePayoff, Params.learnedCost, Params.cost, Params.rate,
    outcomeValue] at hbind ⊢
  have hd : (t.p₂ true - (P.cl - P.rl * t.q₁ * 0) * t.q₂ true) -
      (t.p₂ false - (P.cl - P.rl * t.q₁ * 0) * t.q₂ false) =
      (P.ch - P.rh * t.q₁ - P.cl) * (t.q₂ true - t.q₂ false) := by
    linear_combination hbind
  refine ⟨fun h1 => ?_, fun h1 => ⟨?_, fun h2 => ?_⟩⟩
  · have : (P.ch - P.rh * t.q₁ - P.cl) * (t.q₂ true - t.q₂ false) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have : 0 ≤ (P.ch - P.rh * t.q₁ - P.cl) * (t.q₂ true - t.q₂ false) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  · have : 0 < (P.ch - P.rh * t.q₁ - P.cl) * (t.q₂ true - t.q₂ false) :=
      mul_pos (by linarith) (by linarith)
    linarith
