-- Prove2me | solution 1 for PI.FockOneDegW.RedOps.lowOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:26.422417+00:00
-- url     : https://prove2.me/submissions/daedb1ca-9f46-455c-b964-181a14af4f6e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}
namespace PI.FockOneDegW.RedOps
theorem _root_.solution (c d : Ix r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d P = ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
      pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P) else 0) := by
  unfold lowOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> rfl
end PI.FockOneDegW.RedOps
