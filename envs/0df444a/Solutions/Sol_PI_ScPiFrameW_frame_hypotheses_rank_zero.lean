-- Prove2me | solution 1 for PI.ScPiFrameW.frame_hypotheses_rank_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:17:39.574241+00:00
-- url     : https://prove2.me/submissions/720636e5-6301-4c5c-8119-298b94843dc2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameHypothesesRankZero
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScPiFrameW_hJ_eq_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.ScPiFrameW
open PI.ScPiExists
namespace PI.ScPiFrameW
theorem _root_.solution :
    let ε : Fin 2 → Bool := ![true, false]
    let z : Fin 2 → ℂ := ![0, 1]
    (2 = 2 * 0 + 1 + 1) ∧
    (∀ i : Fin 2, ε i = if i.val < 1 - 1 then true else decide ((i.val - (1 - 1)) % 2 = 0)) ∧
    hJ ε z z = -((1 : ℝ) : ℂ) := by
  intro ε z
  refine ⟨rfl, ?_, ?_⟩
  · intro i; fin_cases i <;> rfl
  · simp [z, ε, hJ_eq_sum, sg, Fin.sum_univ_two]
end PI.ScPiFrameW
