-- Prove2me | solution 1 for PI.HwUniqW.mk_bl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:53.750352+00:00
-- url     : https://prove2.me/submissions/c60b88d5-717f-4e72-82dd-52a3058e9680

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
theorem _root_.solution (c : Fin k) (p : (bl k r c).val - r < k) : (⟨(bl k r c).val - r, p⟩ : Fin k) = c := by
  apply Fin.ext
  show r + c.val - r = c.val
  omega
end PI.HwUniqW
