-- Prove2me | solution 1 for PI.VolStabS.henselCount_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:50.264781+00:00
-- url     : https://prove2.me/submissions/c230729c-4801-4cf8-aec5-06913b1b0676

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_HenselCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_HenselCountHolds
import Theorems.Thm_PI_VolStabS_hensel_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Topology
namespace PI.VolStabS
theorem _root_.solution : HenselCount := by
  intro V X _ _ _ _ _ _ _ _ _ _ μ ν _ _ Λ H hΛo _ hΛa hHo hHc D hD G y hG n h hh
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG h hh n
end PI.VolStabS
