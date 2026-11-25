-- Prove2me | solution 1 for PI.AmpRootCommon.Tri.triShear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:17.373291+00:00
-- url     : https://prove2.me/submissions/a9da855c-f212-41bd-a78c-953bc10c20e1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Theorems.Thm_PI_AmpRootCommon_Tri_measurePreserving_of_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.AmpRootCommon PI.AmpRootCommon.Tri
namespace PI.AmpRootCommon.Tri
theorem _root_.solution : TriShear :=
  fun ι _ _ r g hg hdep => measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep
end PI.AmpRootCommon.Tri
