-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.twist_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:15.442784+00:00
-- url     : https://prove2.me/submissions/d25ac7c2-16cf-47a6-9d36-0bdd0fba4fbd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelTwist
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_det_star_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} (k : KG ε) : (toMK k).det ≠ 0 := by
  intro h
  have h1 := twist_det_star_mul k
  rw [h, mul_zero] at h1
  exact zero_ne_one h1
end ReciprocityTheory.ChartRestriction.DS.HW
