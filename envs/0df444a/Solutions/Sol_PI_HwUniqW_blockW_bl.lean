-- Prove2me | solution 1 for PI.HwUniqW.blockW_bl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:56.77783+00:00
-- url     : https://prove2.me/submissions/c723eece-4126-4501-bba6-46525ea4e6f3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_inB_bl
import Theorems.Thm_PI_HwUniqW_mk_bl
import Theorems.Thm_PI_HwUniqW_blockW_in

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
theorem _root_.solution (h : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    blockW k r h (bl k r a) (bl k r b) = h a b := by
  rw [blockW_in h (inB_bl a) (inB_bl b)]
  simp only [mk_bl]
end PI.HwUniqW
