-- Prove2me | solution 1 for PI.FockOneDegW.Swap.rename_raiB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:17.827282+00:00
-- url     : https://prove2.me/submissions/45054430-c8fc-4ea8-a913-04368d8b60f1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Theorems.Thm_PI_FockOneDegW_Swap_linePos_sw
import Theorems.Thm_PI_FockOneDegW_Swap_rename_X_mul
import Theorems.Thm_PI_FockOneDegW_Swap_rename_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Swap
theorem _root_.solution (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (raiB l P) = raiB (sw p q r s l) (rename (sw p q r s) P) := by
  unfold raiB
  rw [linePos_sw]
  split_ifs
  · exact rename_X_mul l P
  · show rename _ (-(pderiv l P)) = -(pderiv (sw p q r s l) (rename _ P))
    rw [map_neg, rename_pderiv]
end PI.FockOneDegW.Swap
