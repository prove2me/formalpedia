-- Prove2me | solution 1 for PI.AlgValsFin.W.torsUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:48.699881+00:00
-- url     : https://prove2.me/submissions/54e923db-a51f-445d-973e-9b700ee93f13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinOfTors
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_TorsUnitsOfNbhd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Theorems.Thm_PI_AlgValsFin_W_exists_nbhd
import Theorems.Thm_PI_AlgValsFin_W_torsUnits_of_nbhd


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
theorem _root_.solution (L : Type) [Field L] [NumberField L] : TorsUnits L :=
  torsUnits_of_nbhd L fun W hW h1 => exists_nbhd W hW h1
end PI.AlgValsFin.W
