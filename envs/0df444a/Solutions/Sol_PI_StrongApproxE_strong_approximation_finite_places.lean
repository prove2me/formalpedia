-- Prove2me | solution 1 for PI.StrongApproxE.strong_approximation_finite_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:16:09.524919+00:00
-- url     : https://prove2.me/submissions/85b52959-ac60-44de-92a8-c178dc972910

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_StrongApproxE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_LocSmall
import Definitions.Def_Lemmata_Cancellation_EnnrealVolumeRatioStepCancel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Theorems.Thm_PI_StrongApproxE_DedekindLFunctions_sa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open PI PI.StrongApproxE
namespace PI.StrongApproxE
theorem _root_.solution : DedSA := by
  intro F _ _ T a c hc
  exact DedekindLFunctions.sa (R := 𝓞 F) (K := F) T a c hc
end PI.StrongApproxE
