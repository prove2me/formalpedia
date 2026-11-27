-- Prove2me | solution 1 for PI.ScPiFrameW.frame_hypotheses_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:17:34.178271+00:00
-- url     : https://prove2.me/submissions/195cb33f-727e-446b-8544-1f192896c98c

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
    let ε : Fin 4 → Bool := ![true, false, true, false]
    let e : Fin 1 → Fin 4 → ℂ := fun _ => ![1, 1, 0, 0]
    let f : Fin 1 → Fin 4 → ℂ := fun _ => ![1 / 2, -1 / 2, 0, 0]
    let z : Fin 4 → ℂ := ![0, 0, 0, 1]
    (4 = 2 * 1 + 1 + 1) ∧
    (∀ i : Fin 4, ε i = if i.val < 1 - 1 then true else decide ((i.val - (1 - 1)) % 2 = 0)) ∧
    (∀ a b, hJ ε (e a) (e b) = 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
    (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧
    (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) ∧ hJ ε z z = -((1 : ℝ) : ℂ) := by
  intro ε e f z
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> rfl
  · intro a b; simp [e, ε, hJ_eq_sum, sg, Fin.sum_univ_four]
  · intro a b; simp [f, ε, hJ_eq_sum, sg, Fin.sum_univ_four]; ring
  · intro a b
    have : a = b := Subsingleton.elim a b
    simp [this, e, f, ε, hJ_eq_sum, sg, Fin.sum_univ_four]; ring
  · intro a; simp [e, f, z, ε, hJ_eq_sum, sg, Fin.sum_univ_four]
  · simp [z, ε, hJ_eq_sum, sg, Fin.sum_univ_four]
end PI.ScPiFrameW
