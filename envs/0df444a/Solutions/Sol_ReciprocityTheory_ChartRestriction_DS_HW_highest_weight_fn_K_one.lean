-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.highest_weight_fn_K_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:45.726262+00:00
-- url     : https://prove2.me/submissions/2af5a407-f099-42e1-9259-658fe14aaafd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m 1 = 1 := by
  have h1 : toMK (1 : KG ε) = 1 := by
    first
      | exact toMK_one
      | simp [toMK]
      | rfl
  unfold f0K f0 blkMinor
  rw [h1]
  simp [Matrix.submatrix_one _ Subtype.val_injective]
end ReciprocityTheory.ChartRestriction.DS.HW
