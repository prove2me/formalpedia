-- Prove2me | solution 1 for PI.HwUniqW.mem_UJset_allPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:53.009329+00:00
-- url     : https://prove2.me/submissions/74678015-73c5-4cb5-ad80-abf12833051a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_Jm_allPos

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
theorem _root_.solution {h : Matrix (Fin k) (Fin k) ℂ} : h ∈ UJset (allPos k) ↔ hᴴ * h = 1 := by
  show inUJ (allPos k) h ↔ hᴴ * h = 1
  unfold inUJ
  rw [Jm_allPos, mul_one]
end PI.HwUniqW
