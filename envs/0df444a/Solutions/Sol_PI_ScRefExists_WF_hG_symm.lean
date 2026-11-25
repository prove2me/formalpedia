-- Prove2me | solution 1 for PI.ScRefExists.WF.hG_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:18.8658+00:00
-- url     : https://prove2.me/submissions/3ddaea65-41b9-4e19-b730-5088e312d2f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Theorems.Thm_PI_ScRefExists_WF_hG_def
import Theorems.Thm_PI_ScRefExists_WF_J_entry
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
theorem _root_.solution (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  simp only [hG_def, star_sum, star_mul', star_star]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [J_entry I a b]
  ring
end PI.ScRefExists.WF
