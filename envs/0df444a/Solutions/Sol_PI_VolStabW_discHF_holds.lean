-- Prove2me | solution 1 for PI.VolStabW.discHF_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:51.917598+00:00
-- url     : https://prove2.me/submissions/20f6ab26-7ead-46d3-95a7-a9a56aede82d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExFDStab
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoClose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExFDStabFin
import Theorems.Thm_PI_VolSemiDirect_W_Lc_tensor_adele_topology_holds
import Theorems.Thm_PI_VolSemiDirect_W_discHA_of
import Theorems.Thm_PI_VolStabW_discHF_of_discHA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution : DiscHF :=
  discHF_of_discHA (PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds)
end PI.VolStabW
