-- Prove2me | solution 1 for PI.ScRefExists.PPA.hG_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:30.988085+00:00
-- url     : https://prove2.me/submissions/19818276-fcbf-4810-9c17-34938af2ce2d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Theorems.Thm_PI_ScRefExists_PPA_hG_add_left
import Theorems.Thm_PI_ScRefExists_PPA_hG_neg_left

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
theorem _root_.solution (x x' y : Fin I.n → I.E) : hG I (x - x') y = hG I x y - hG I x' y := by
  rw [sub_eq_add_neg, hG_add_left, hG_neg_left, ← sub_eq_add_neg]
end PI.ScRefExists.PPA
