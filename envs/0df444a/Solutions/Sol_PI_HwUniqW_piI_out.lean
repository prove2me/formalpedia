-- Prove2me | solution 1 for PI.HwUniqW.piI_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:54.383529+00:00
-- url     : https://prove2.me/submissions/672b4c9d-b12b-4ae9-baec-48028eebd844

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
theorem _root_.solution {i : Fin (2 * r + k + 1)} (hi : ¬ InB k r i) : ¬ InB k r (piI k r i) := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  have h0 := i.isLt
  unfold piI InB
  split_ifs with h
  · exact hi'
  · show ¬ (r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val < r + k)
    omega
end PI.HwUniqW
