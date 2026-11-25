-- Prove2me | solution 1 for PI.SelfDualLoc.W.locBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:31.66539+00:00
-- url     : https://prove2.me/submissions/6ff97593-96d6-4c9c-9265-f14cb60e9aa7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Lemmata_PaddedFamilies_PadFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_LocBasis
import Theorems.Thm_Bl_PaddedFamilies_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc LB
namespace PI.SelfDualLoc.W
theorem _root_.solution : LocBasis := by
  first | exact Bl.PaddedFamilies.goal1 .. | (apply Bl.PaddedFamilies.goal1 <;> assumption) | (intros; apply Bl.PaddedFamilies.goal1 <;> assumption)
end PI.SelfDualLoc.W
