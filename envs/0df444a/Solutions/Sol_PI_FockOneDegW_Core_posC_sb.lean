-- Prove2me | solution 1 for PI.FockOneDegW.Core.posC_sb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:14.759749+00:00
-- url     : https://prove2.me/submissions/4e77ecbc-e8c1-49cc-9ad4-1a065f337b45

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
theorem _root_.solution {m n : ℕ} (a b : Ix m n) (h : posC a b) : sameBlock a b := by
  rcases a with i | i <;> rcases b with j | j <;> simp_all [posC, sameBlock]
end PI.FockOneDegW.Core
