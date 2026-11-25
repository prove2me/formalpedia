-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.differentiable_highest_weight_fn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:51.521751+00:00
-- url     : https://prove2.me/submissions/739ff930-178d-425d-8f9a-8c51fa38c9a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_diff_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_diff_blkMinor

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
theorem _root_.solution (ε : Fin n → Bool) (m : Fin n → ℤ) : Differentiable ℂ (f0 ε m) := by
  show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => f0 ε m x)
  simp only [f0]
  exact hwmf_diff_prod _ _ (fun a => (hwmf_diff_blkMinor ε a).pow _)
end ReciprocityTheory.ChartRestriction.DS.HW
