-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.mult_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:03.916968+00:00
-- url     : https://prove2.me/submissions/b786b985-4ae4-49bc-8154-78ff7901cd5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lgS_subst_uSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_constantCoeff_C_mul_weierstrassLog

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
theorem _root_.solution (b : K) :
    (lgS g2 g3).subst ((uSer g2 g3).subst (C b * lgS g2 g3)) = C b * lgS g2 g3 := by
  have hu := HasSubst.of_constantCoeff_zero (uSer_const g2 g3)
  have ha := HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_weierstrassLog g2 g3 b)
  have h1 := PowerSeries.subst_comp_subst_apply hu ha (lgS g2 g3)
  rw [lgS_subst_uSer, PowerSeries.subst_X ha] at h1
  exact h1.symm
end ReciprocityTheory.ChartRestriction.L1
