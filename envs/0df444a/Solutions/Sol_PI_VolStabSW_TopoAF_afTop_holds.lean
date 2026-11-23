-- Prove2me | solution 1 for PI.VolStabSW.TopoAF.afTop_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:39.153977+00:00
-- url     : https://prove2.me/submissions/c34ce0df-d71d-4bae-b732-1f71d224d60c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TensTopOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabSW PI.VolStabSW.TopoAF
namespace PI.VolStabSW.TopoAF
theorem _root_.solution : PI.VolSemiDirect.W.Lc.AFTop := fun F _ _ =>
  ⟨inferInstance, inferInstance, inferInstance⟩
end PI.VolStabSW.TopoAF
