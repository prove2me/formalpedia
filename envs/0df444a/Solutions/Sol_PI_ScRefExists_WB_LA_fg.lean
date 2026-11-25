-- Prove2me | solution 1 for PI.ScRefExists.WB.LA_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:19.142886+00:00
-- url     : https://prove2.me/submissions/3958f803-5d1b-47a8-a60d-2b1f9e46fbe9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WeilBasisExistence

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
open PI PI.ScRefExists PI.ScRefExists.WB
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.WB
theorem _root_.solution (p : ℕ) : (LA I p).FG := by
  obtain ⟨s, hs⟩ := I.L_fg
  refine ⟨s, ?_⟩
  unfold LA
  rw [← hs, Submodule.span_span_of_tower]
end PI.ScRefExists.WB
