-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.lgS_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:42:54.918186+00:00
-- url     : https://prove2.me/submissions/2e56f0ba-8f26-49a5-a7dc-9b15aa5464a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_one_subst_of_constantCoeff_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lgS_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_subst_lgS

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
theorem _root_.solution : coeff 1 (lgS g2 g3) = 1 := by
  have h := congrArg (coeff 1) (uSer_subst_lgS g2 g3)
  rw [coeff_one_subst_of_constantCoeff_eq_zero _ _ (lgS_const g2 g3), uSer_coeff_one, one_mul] at h
  simpa using h
end ReciprocityTheory.ChartRestriction.L1
