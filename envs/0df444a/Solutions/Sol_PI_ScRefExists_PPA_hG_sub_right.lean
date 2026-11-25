-- Prove2me | solution 1 for PI.ScRefExists.PPA.hG_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:03.572074+00:00
-- url     : https://prove2.me/submissions/4999c339-32c8-4b9f-be05-6b2d03442cc2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Theorems.Thm_PI_ScRefExists_PPA_hG_add_right
import Theorems.Thm_PI_ScRefExists_PPA_hG_neg_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (x y y' : Fin I.n → I.E) : hG I x (y - y') = hG I x y - hG I x y' := by
  rw [sub_eq_add_neg, hG_add_right, hG_neg_right, ← sub_eq_add_neg]
end PI.ScRefExists.PPA
