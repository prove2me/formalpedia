-- Prove2me | solution 1 for PI.FockOneDegW.Swap.rename_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:00.888243+00:00
-- url     : https://prove2.me/submissions/e6bd0f2f-436d-45ae-a6c1-2773d844bfd2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap

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
    rename (sw p q r s) (X l * P) = X (sw p q r s l) * rename (sw p q r s) P := by
  rw [map_mul, rename_X]
end PI.FockOneDegW.Swap
