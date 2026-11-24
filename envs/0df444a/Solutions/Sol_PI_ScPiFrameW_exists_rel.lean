-- Prove2me | solution 1 for PI.ScPiFrameW.exists_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:00.017181+00:00
-- url     : https://prove2.me/submissions/b435f974-29ce-40d2-b4f3-b07bf5d23f34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
namespace PI.ScPiFrameW
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (v : κ → ι → ℂ)
    (h : Fintype.card ι < Fintype.card κ) : ∃ g : κ → ℂ, ∑ j, g j • v j = 0 ∧ ∃ j, g j ≠ 0 := by
  apply Fintype.not_linearIndependent_iff.mp
  intro hli
  have := hli.fintype_card_le_finrank
  simp at this
  omega
end PI.ScPiFrameW
