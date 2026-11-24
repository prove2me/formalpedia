-- Prove2me | solution 1 for PI.FockOneDegW.Core.posOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:26.506667+00:00
-- url     : https://prove2.me/submissions/55f9ccce-2615-4674-b1e6-d212042f35ff

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
theorem _root_.solution (v : Pol p q r s) (a b : Ix p q) :
    posOp a b v = ∑ d : Ix r s, (if linePos ((a, d) : Ln p q r s) = true then
      X ((a, d) : Ln p q r s) * pderiv ((b, d) : Ln p q r s) v else 0) := by
  unfold posOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hl : linePos ((a, d) : Ln p q r s) = true
  · simp [hl]
  · simp [hl]
end PI.FockOneDegW.Core
