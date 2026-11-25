-- Prove2me | solution 1 for PI.VolStabW.henselCount_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:10.934426+00:00
-- url     : https://prove2.me/submissions/89ea3fef-32ae-4d94-afc1-2622753743e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCountHolds
import Theorems.Thm_PI_VolStabW_hensel_main

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
open MeasureTheory Topology
namespace PI.VolStabW
theorem _root_.solution : HenselCount := by
  intro V X _ _ _ _ _ _ _ _ _ _ μ ν hμ hν Λ H hΛo _ hΛa hHo hHc D hD G y hG n h hh
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG h hh n
end PI.VolStabW
