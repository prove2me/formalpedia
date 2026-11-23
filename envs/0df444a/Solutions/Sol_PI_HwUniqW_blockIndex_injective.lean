-- Prove2me | solution 1 for PI.HwUniqW.blockIndex_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:52.810975+00:00
-- url     : https://prove2.me/submissions/7d4b108b-1b5d-4052-82ac-51449b05adf4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution : Function.Injective (bl k r) := by
  intro a b h
  have h' := congrArg Fin.val h
  change r + a.val = r + b.val at h'
  exact Fin.ext (by omega)
end PI.HwUniqW
