-- Prove2me | solution 1 for PI.AlgValsFin.W.algValsFin_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:22.624826+00:00
-- url     : https://prove2.me/submissions/56683a77-9643-4369-86bb-abcd2c12655f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinOfTors
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_TorsUnitsOfNbhd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Theorems.Thm_PI_AlgValsFin_W_torsUnits
import Theorems.Thm_PI_AlgValsFin_W_algValsFin_of_tors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AlgValsFin PI.AlgValsFin.W
namespace PI.AlgValsFin.W
theorem _root_.solution (L : Type) [Field L] [NumberField L] : AlgValsFin L :=
  algValsFin_of_tors L (torsUnits L)
end PI.AlgValsFin.W
