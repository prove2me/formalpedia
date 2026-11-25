-- Prove2me | solution 1 for PI.VolStabSW.discHF_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:12.865373+00:00
-- url     : https://prove2.me/submissions/e118f4a9-e103-4a75-b67e-a5c16cd9d38a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExFDStab
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoClose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExFDStabFin
import Theorems.Thm_PI_VolSemiDirect_W_Lc_tensor_adele_topology_holds
import Theorems.Thm_PI_VolSemiDirect_W_discHA_of
import Theorems.Thm_PI_VolStabSW_discHF_of_discHA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabSW
namespace PI.VolStabSW
theorem _root_.solution : DiscHF :=
  discHF_of_discHA (PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds)
end PI.VolStabSW
