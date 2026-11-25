-- Prove2me | solution 1 for PI.ArtSch.WittLiftWork.wittLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:06:15.157806+00:00
-- url     : https://prove2.me/submissions/348b026a-4ece-4b61-b4ac-10c9aa8d79ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem
import Theorems.Thm_PI_ArtSch_WittLiftWork_lim_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.WittLiftWork
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]
namespace PI.ArtSch.WittLiftWork
theorem _root_.solution : PI.ArtSch.WittLift := by
  intro p _ k _ _ hAS x
  exact ⟨lim hAS x, lim_spec hAS x⟩
end PI.ArtSch.WittLiftWork
