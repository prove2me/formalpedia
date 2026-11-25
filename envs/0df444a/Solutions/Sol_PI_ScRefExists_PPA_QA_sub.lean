-- Prove2me | solution 1 for PI.ScRefExists.PPA.QA_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:52.844336+00:00
-- url     : https://prove2.me/submissions/af2b167b-b1b3-4c65-a1a6-5679ced9a340

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Theorems.Thm_PI_ScRefExists_PPA_QA_add
import Theorems.Thm_PI_ScRefExists_PPA_QA_neg

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
theorem _root_.solution (p q : ℕ) {x y : I.E} (hx : QA I p q x) (hy : QA I p q y) : QA I p q (x - y) := by
  rw [sub_eq_add_neg]
  exact QA_add I p q hx (QA_neg I p q hy)
end PI.ScRefExists.PPA
