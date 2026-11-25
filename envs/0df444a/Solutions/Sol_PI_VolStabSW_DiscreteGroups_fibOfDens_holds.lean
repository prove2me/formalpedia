-- Prove2me | solution 1 for PI.VolStabSW.DiscreteGroups.fibOfDens_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:16.744799+00:00
-- url     : https://prove2.me/submissions/70b84ba6-4176-44d3-93cb-a358068a9528

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibDis
import Theorems.Thm_PI_VolStabSW_DiscreteGroups_disintStep_holds
import Theorems.Thm_PI_VolStabSW_Glue_fibOfDens_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabSW PI.VolStabSW.Glue
open scoped ENNReal
namespace PI.VolStabSW.DiscreteGroups
theorem _root_.solution : FibOfDens := fibOfDens_of disintStep_holds
end PI.VolStabSW.DiscreteGroups
