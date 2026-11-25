-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.lgS_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:06.645136+00:00
-- url     : https://prove2.me/submissions/75c1f797-2854-439c-a370-4aa94bd421d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lgS_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_subst_lgS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lgS_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_map_subst_ps

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
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : PowerSeries.map φ (lgS g2 g3) = lgS (φ g2) (φ g3) := by
  refine lgS_unique (φ g2) (φ g3) _ ?_ ?_
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      lgS_const, map_zero]
  · rw [← uSer_map, ← map_subst_ps φ (lgS_const g2 g3), uSer_subst_lgS, map_X]
end ReciprocityTheory.ChartRestriction.L1
