-- Prove2me | solution 1 for PI.HwUniqW.inB_bl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:51.550797+00:00
-- url     : https://prove2.me/submissions/049e526f-dcca-4488-bc1c-547eed8e2dff

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
theorem _root_.solution (a : Fin k) : InB k r (bl k r a) := by
  have := a.isLt
  show r ≤ (bl k r a).val ∧ (bl k r a).val < r + k
  show r ≤ r + a.val ∧ r + a.val < r + k
  omega
end PI.HwUniqW
