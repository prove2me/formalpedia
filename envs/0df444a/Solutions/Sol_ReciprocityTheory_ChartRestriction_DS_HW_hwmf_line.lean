-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:22.256807+00:00
-- url     : https://prove2.me/submissions/a44a1b77-9b8c-436e-ba17-9f5bec350a44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_differentiable_highest_weight_fn

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
theorem _root_.solution (ε : Fin n → Bool) (m : Fin n → ℤ) (x W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℂ => f0 ε m (x * (1 + s • W))) (fderiv ℂ (f0 ε m) x (x * W)) 0 := by
  have hin : HasDerivAt (fun s : ℂ => x * (1 + s • W)) (x * W) 0 := by
    have hfun : (fun s : ℂ => x * (1 + s • W)) = fun s => x + s • (x * W) := by
      funext s
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [hfun]
    have h := ((hasDerivAt_id' (0 : ℂ)).smul_const (x * W)).const_add x
    rw [one_smul] at h
    exact h
  have hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) x) (x * (1 + (0 : ℂ) • W)) := by
    rw [zero_smul, add_zero, Matrix.mul_one]
    exact (differentiable_highest_weight_fn ε m x).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℂ) hin
end ReciprocityTheory.ChartRestriction.DS.HW
