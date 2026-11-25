-- Prove2me | solution 1 for PI.WA.weakApproxDVR_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:47.459085+00:00
-- url     : https://prove2.me/submissions/7dbf9215-e524-45e6-a695-d2dbd8bc9413

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeakApproxDVR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WA
namespace PI.WA
theorem _root_.solution (hB : BigExists) (hA : Assembly) : PI.WeakApproxDVR := by
  intro E _ ι _ W Q _ _ _ _ _ _ iw p hp hpu hloc hsep x N
  choose ϖ hϖ using fun i => IsDiscreteValuationRing.exists_irreducible (W i)
  exact hA E ι W Q iw p hp hpu hloc ϖ hϖ (hB E ι W Q iw p hp hpu hloc hsep ϖ hϖ) x N
end PI.WA
