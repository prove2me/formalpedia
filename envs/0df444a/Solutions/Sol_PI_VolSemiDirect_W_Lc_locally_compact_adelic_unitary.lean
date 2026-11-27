-- Prove2me | solution 1 for PI.VolSemiDirect.W.Lc.locally_compact_adelic_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:44.70065+00:00
-- url     : https://prove2.me/submissions/ad5293a8-a1c9-4e5b-9fc7-5d5291837c07

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LcscHAOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Theorems.Thm_PI_VolSemiDirect_W_Lc_tensor_adele_topology_holds
import Theorems.Thm_PI_VolSemiDirect_W_Lc_lcscHA_of


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
theorem _root_.solution : LcscHA := lcscHA_of tensor_adele_topology_holds
end PI.VolSemiDirect.W.Lc
