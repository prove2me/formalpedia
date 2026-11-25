-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.lgS_subst_uSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:38:03.85213+00:00
-- url     : https://prove2.me/submissions/9bfb257c-8eb4-496f-abac-bfda2b0cd326

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_weierstrassLog_eq_substInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [Field K] (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : (lgS g2 g3).subst (uSer g2 g3) = X := by
  rw [weierstrassLog_eq_substInv]
  exact PowerSeries.subst_substInvOfIsUnit_left _ (uSer_const g2 g3) _
end ReciprocityTheory.ChartRestriction.L1
