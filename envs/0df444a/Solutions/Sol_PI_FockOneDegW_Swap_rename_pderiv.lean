-- Prove2me | solution 1 for PI.FockOneDegW.Swap.rename_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:53.433108+00:00
-- url     : https://prove2.me/submissions/4bb96631-6ab8-4d20-9528-213373b61277

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
    rename (sw p q r s) (pderiv l P) = pderiv (sw p q r s l) (rename (sw p q r s) P) := (pderiv_rename (sw p q r s).injective l P).symm
end PI.FockOneDegW.Swap
