-- Prove2me | solution 1 for PI.FockOneDegW.Core.side_lp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:18.776557+00:00
-- url     : https://prove2.me/submissions/621f1598-0c92-4f9b-999f-884aa0dd818b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution (a : Ix p q) (c : Ix r s) :
    linePos ((a, c) : Ln p q r s) = true ↔ a.isLeft = c.isLeft := by
  rcases a with i | i <;> rcases c with j | j <;> simp [linePos]
end PI.FockOneDegW.Core
