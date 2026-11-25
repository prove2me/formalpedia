-- Prove2me | solution 1 for PI.ScRefExists.PPA.QA_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:58.32748+00:00
-- url     : https://prove2.me/submissions/75029828-6b26-4e6a-917a-2e2fdca8141e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL

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
theorem _root_.solution (p q : ℕ) {x : I.E} (hx : QA I p q x) : QA I p q (-x) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  refine ⟨s, hs, -a, ?_⟩
  push_cast
  linear_combination -ha
end PI.ScRefExists.PPA
