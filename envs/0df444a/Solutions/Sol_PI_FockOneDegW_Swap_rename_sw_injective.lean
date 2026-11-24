-- Prove2me | solution 1 for PI.FockOneDegW.Swap.rename_sw_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:24.954913+00:00
-- url     : https://prove2.me/submissions/6cbcd8fb-eeeb-43e9-933a-2ac37b3f0e10

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
theorem _root_.solution (p q r s : ℕ) :
    Function.Injective (rename (R := ℂ) (sw p q r s)) := rename_injective _ (sw p q r s).injective
end PI.FockOneDegW.Swap
