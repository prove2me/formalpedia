-- Prove2me | solution 1 for PI.WeylForKWork.rhoC_eMi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:07.154986+00:00
-- url     : https://prove2.me/submissions/e1fdaf06-3610-4b11-a5c1-ea842ccaa17c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
import Theorems.Thm_PI_WeylForKWork_prod_split
import Theorems.Thm_PI_WeylForKWork_card_gt_eMi
import Theorems.Thm_PI_WeylForKWork_card_lt_eMi
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
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution (ε : Fin N → Bool) (i : Fin (nMi ε)) :
    rhoC ε (eMi ε i) = ((nMi ε : ℝ) - 1 - 2 * (i : ℕ)) / 2 := by
  simp only [rhoC]
  rw [card_gt_eMi, card_lt_eMi]
  have hi := i.isLt
  have h1 : (i : ℕ) ≤ nMi ε - 1 := by omega
  have h2 : 1 ≤ nMi ε := by omega
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  push_cast
  ring
end PI.WeylForKWork
