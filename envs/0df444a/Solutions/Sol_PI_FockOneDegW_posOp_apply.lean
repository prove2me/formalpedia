-- Prove2me | solution 1 for PI.FockOneDegW.posOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:37.694799+00:00
-- url     : https://prove2.me/submissions/0a13c793-aec1-464b-8b8c-5965497a048e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel

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
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    posOp a b P = ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then
      X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P else 0) := by
  unfold posOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
end PI.FockOneDegW
