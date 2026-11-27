-- Prove2me | solution 1 for PI.VolStabSW.finTheta_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:30.715147+00:00
-- url     : https://prove2.me/submissions/a9747579-9ca9-4e00-8d9f-a90c2e38bad9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_finite_of_adm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace PI.VolStabSW
theorem _root_.solution : FinTheta := by
  intro F E _ _ _ _ _ σ _ M J _ _ _ a _ _ X0 hT _ Φ hΦ h
  exact FiniteThetaCoordinates.finite_of_adm Φ hΦ _
end PI.VolStabSW
