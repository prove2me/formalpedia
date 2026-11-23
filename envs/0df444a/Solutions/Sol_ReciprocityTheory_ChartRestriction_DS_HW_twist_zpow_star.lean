-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.twist_zpow_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:14.937472+00:00
-- url     : https://prove2.me/submissions/90917d96-bf5c-4742-9180-236d3cb0e2f2

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
theorem _root_.solution {ε : Fin n → Bool} (k : KG ε) (c : ℤ) :
    star ((toMK k).det ^ c) * (toMK k).det ^ c = 1 := by
  rw [star_zpow₀, ← _root_.mul_zpow, twist_det_star_mul, _root_.one_zpow]
end ReciprocityTheory.ChartRestriction.DS.HW
