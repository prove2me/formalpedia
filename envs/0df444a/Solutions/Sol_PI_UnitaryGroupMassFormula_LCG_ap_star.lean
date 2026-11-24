-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:54:47.771892+00:00
-- url     : https://prove2.me/submissions/4621ab68-8f82-4396-af79-369a5a2b16f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (v : InfinitePlace I.F) (a : I.E) : I.φ v (star a) = star (I.φ v a) := by
  have h := I.cm.cmUnram.2.1 (I.φ v) a
  rw [starRingEnd_apply] at h
  exact h
end PI.UnitaryGroupMassFormula.LCG
