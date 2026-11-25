-- Prove2me | solution 1 for PI.VolStabW.finTheta_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:33.033869+00:00
-- url     : https://prove2.me/submissions/74193ee7-fd71-438c-b425-01346d0870fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_finite_of_adm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace PI.VolStabW
theorem _root_.solution : FinTheta := by
  intro F E _ _ _ _ _ σ _ M J _ _ _ a _ _ X0 hT _ Φ hΦ h
  exact FiniteThetaCoordinates.finite_of_adm Φ hΦ _
end PI.VolStabW
