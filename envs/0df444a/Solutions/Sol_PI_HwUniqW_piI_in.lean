-- Prove2me | solution 1 for PI.HwUniqW.piI_in
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:54.093166+00:00
-- url     : https://prove2.me/submissions/fa36da83-6e02-4a7e-bdc5-79a7ca1b41ab

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
theorem _root_.solution {i : Fin (2 * r + k + 1)} (hi : InB k r i) : piI k r i = i := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  unfold piI
  rw [if_pos (by omega)]
end PI.HwUniqW
