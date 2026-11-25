-- Prove2me | solution 1 for PI.VolStabW.DiscreteGroups.fibOfDens_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:23.145392+00:00
-- url     : https://prove2.me/submissions/3c860412-0b87-463e-ac2e-167aaa4c0736

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibDis
import Theorems.Thm_PI_VolStabW_DiscreteGroups_disintStep_holds
import Theorems.Thm_PI_VolStabW_Glue_fibOfDens_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabW PI.VolStabW.Glue
open scoped ENNReal
namespace PI.VolStabW.DiscreteGroups
theorem _root_.solution : FibOfDens := fibOfDens_of disintStep_holds
end PI.VolStabW.DiscreteGroups
