-- Prove2me | solution 1 for PI.WeylForKWork.mem_unitaryCentralizer_allPos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:34:53.274811+00:00
-- url     : https://prove2.me/submissions/80461812-4e06-4f60-8324-578e88ba4953

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_signatureMatrix_allPos_eq_one
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
open PI PI.UpqRep Matrix
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : h ∈ Kset (allPos n) ↔ h ∈ unitaryGroup _ ℂ := by
  show h ∈ unitaryGroup _ ℂ ∧ h * Jm (allPos n) = Jm (allPos n) * h ↔ _
  rw [signatureMatrix_allPos_eq_one]
  simp
end PI.WeylForKWork
