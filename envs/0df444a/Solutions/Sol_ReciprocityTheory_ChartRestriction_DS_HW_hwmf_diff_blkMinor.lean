-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_diff_blkMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:26.971027+00:00
-- url     : https://prove2.me/submissions/6a264f19-ec96-4675-bb6a-336d3458e3e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_diff_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_diff_prod

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
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) : Differentiable ℂ (blkMinor ε a) := by
  show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => blkMinor ε a x)
  simp only [blkMinor, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  first
    | (apply Differentiable.fun_sum
       intro σ _
       exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))
    | fun_prop
    | (apply Differentiable.sum
       intro σ _
       exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))
end ReciprocityTheory.ChartRestriction.DS.HW
