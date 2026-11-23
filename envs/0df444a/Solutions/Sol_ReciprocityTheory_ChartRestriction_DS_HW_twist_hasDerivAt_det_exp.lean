-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.twist_hasDerivAt_det_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:26.31202+00:00
-- url     : https://prove2.me/submissions/1bcafc57-021c-443d-8590-773ecfcdf10c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelTwist
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_hasDerivAt_det_of_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
private theorem hasDerivAt_exp_smul_apply_zero (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : ∀ t : ℝ, ((t : ℂ) • X) = t • X := fun t => Complex.coe_smul t X
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [hc]
  exact h2
end ReciprocityTheory.ChartRestriction.DS.HW
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det) X.trace 0 := by
  refine InhabA.hasDerivAt_det_of_one (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X ?_
    (fun i j => hasDerivAt_exp_smul_apply_zero X i j)
  simp
end ReciprocityTheory.ChartRestriction.DS.HW
