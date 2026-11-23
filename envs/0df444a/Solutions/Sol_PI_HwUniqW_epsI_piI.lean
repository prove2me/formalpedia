-- Prove2me | solution 1 for PI.HwUniqW.epsI_piI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:54.157023+00:00
-- url     : https://prove2.me/submissions/a97ba0d2-06f8-429d-9bb5-a940e68e30fe

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Theorems.Thm_PI_HwUniqW_piI_val

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by
  have := i.isLt
  simp only [epsI, piI_val]
  split_ifs <;> first | rfl | omega
end PI.HwUniqW
