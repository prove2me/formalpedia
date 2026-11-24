-- Prove2me | solution 1 for PI.FockWtDegWork.abs_le_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:43.337183+00:00
-- url     : https://prove2.me/submissions/10e68d16-0b20-41a3-af15-26e190061d84

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution (x A B : ℚ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : x = A - B) : |x| ≤ A + B := by
  rw [hx, abs_le]
  constructor <;> linarith
end PI.FockWtDegWork
