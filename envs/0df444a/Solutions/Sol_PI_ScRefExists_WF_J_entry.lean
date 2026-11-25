-- Prove2me | solution 1 for PI.ScRefExists.WF.J_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:31.661067+00:00
-- url     : https://prove2.me/submissions/741e5146-1b99-43dc-88c8-4fb5c343fd51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
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
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open Matrix
open PI PI.ScRefExists PI.ScRefExists.WF
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.WF
theorem _root_.solution (i j : Fin I.n) : star (I.J j i) = I.J i j := by
  have h : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
  have h2 := congrFun (congrFun h i) j
  simpa [Formalism.UG.cT, starRingEnd_apply] using h2
end PI.ScRefExists.WF
