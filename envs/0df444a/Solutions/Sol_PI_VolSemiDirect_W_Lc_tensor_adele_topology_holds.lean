-- Prove2me | solution 1 for PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:20:18.10555+00:00
-- url     : https://prove2.me/submissions/87801d20-5fa4-4857-967e-3460d2fd63e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LcscHAOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Theorems.Thm_PI_VolSemiDirect_W_Lc_tensTop_of
import Theorems.Thm_PI_VolStabSW_TopoAF_afTop_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Lc
namespace PI.VolSemiDirect.W.Lc
theorem _root_.solution : TensTop := tensTop_of PI.VolStabSW.TopoAF.afTop_holds
end PI.VolSemiDirect.W.Lc
