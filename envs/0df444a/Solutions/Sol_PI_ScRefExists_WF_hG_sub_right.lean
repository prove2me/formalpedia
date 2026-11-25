-- Prove2me | solution 1 for PI.ScRefExists.WF.hG_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:28.69312+00:00
-- url     : https://prove2.me/submissions/94b8b72f-f635-46b3-bc2f-3fc4ffc9063c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Theorems.Thm_PI_ScRefExists_WF_hG_add_right
import Theorems.Thm_PI_ScRefExists_WF_hG_neg_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open Matrix
open PI PI.ScRefExists PI.ScRefExists.WF
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.WF
theorem _root_.solution (x y z : Fin I.n → I.E) : hG I x (y - z) = hG I x y - hG I x z := by
  rw [sub_eq_add_neg, hG_add_right, hG_neg_right, ← sub_eq_add_neg]
end PI.ScRefExists.WF
