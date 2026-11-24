-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.weierstrassLog_eq_substInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:53.28621+00:00
-- url     : https://prove2.me/submissions/dbe672b4-7111-4942-aef1-6579d8620943

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lgS_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_subst_lgS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eq_substInv_of_rightInverse

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
theorem _root_.solution : lgS g2 g3 = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := eq_substInv_of_rightInverse g2 g3 (lgS g2 g3) (lgS_const g2 g3) (uSer_subst_lgS g2 g3)
end ReciprocityTheory.ChartRestriction.L1
