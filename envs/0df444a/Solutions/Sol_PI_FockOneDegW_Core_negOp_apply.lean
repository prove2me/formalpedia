-- Prove2me | solution 1 for PI.FockOneDegW.Core.negOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:26.465807+00:00
-- url     : https://prove2.me/submissions/139c6385-4647-4c90-a104-ecf3e2662814

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
theorem _root_.solution (v : Pol p q r s) (b a : Ix p q) :
    negOp b a v = ∑ c : Ix r s, (if linePos ((b, c) : Ln p q r s) = true then 0
      else X ((b, c) : Ln p q r s) * pderiv ((a, c) : Ln p q r s) v) := by
  unfold negOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hl : linePos ((b, c) : Ln p q r s) = true
  · simp [hl]
  · simp [hl]
end PI.FockOneDegW.Core
