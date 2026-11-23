-- Prove2me | solution 1 for PI.AdCpctDenWork.isOpen_intAd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.084019+00:00
-- url     : https://prove2.me/submissions/87c7a4ee-d6c9-4158-b067-f9f9ab934a5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AdCpctDenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.AdCpctDenWork
theorem _root_.solution : IsOpen (intAd F) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)
end PI.AdCpctDenWork
