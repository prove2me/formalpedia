-- Prove2me | solution 1 for PI.FJMX.negPart_pw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:58.274111+00:00
-- url     : https://prove2.me/submissions/faef18a1-06b0-4406-96e2-265586f03331

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
namespace PI.FJMX
theorem _root_.solution (b : List ℤ) (hb : b.Pairwise (· ≥ ·)) : (PI.FJM.negPart b).Pairwise (· ≥ ·) := by
  rw [PI.FJM.negPart, List.pairwise_reverse, List.pairwise_map]
  exact hb.imp fun h => by omega
end PI.FJMX
