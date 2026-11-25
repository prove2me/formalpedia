-- Prove2me | solution 1 for PI.SqfRootsInj.W.local_orbit_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:15.65699+00:00
-- url     : https://prove2.me/submissions/703228e6-c420-489d-93f9-704f78815f68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour
import Theorems.Thm_PI_SqfRootsInj_W_sums_le
import Theorems.Thm_PI_SqfRootsInj_W_card_le_SA_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution : Count := by
  intro g r _ _ hg T hT
  have h1 := card_le_SA_SB g r T hT
  calc (T.card : ℝ) ≤ ((SA g r + SB g r : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ _ := sums_le g r hg
end PI.SqfRootsInj.W
