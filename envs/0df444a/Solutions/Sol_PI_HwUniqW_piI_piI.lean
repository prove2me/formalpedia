-- Prove2me | solution 1 for PI.HwUniqW.piI_piI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:57.835886+00:00
-- url     : https://prove2.me/submissions/48e11635-a5f2-424f-9aed-5727fd22147d

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [piI_val]
  split_ifs <;> omega
end PI.HwUniqW
