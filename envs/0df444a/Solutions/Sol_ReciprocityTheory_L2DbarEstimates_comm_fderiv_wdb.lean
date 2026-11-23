-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.comm_fderiv_wdb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:23.989061+00:00
-- url     : https://prove2.me/submissions/29cdb450-c981-4d50-a0ab-2e5ed58b6929

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_comm_fderiv_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j : Fin n) (v : V n) :
    fderiv ℝ (wdb n j g) y v = (fderiv ℝ (fderiv ℝ g) y v (bas n j)
      + Complex.I * fderiv ℝ (fderiv ℝ g) y v (Complex.I • bas n j)) * (2 : ℂ)⁻¹ := by
  have hA := comm_fderiv_apply g y hg (bas n j)
  have hB := comm_fderiv_apply g y hg (Complex.I • bas n j)
  have hW : HasFDerivAt (fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      + Complex.I • fderiv ℝ g y' (Complex.I • bas n j))) _ y := (hA.add (hB.const_smul Complex.I)).const_smul (2 : ℂ)⁻¹
  have hfun : wdb n j g = fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      + Complex.I • fderiv ℝ g y' (Complex.I • bas n j)) := by
    funext y'
    simp only [wdb, smul_eq_mul]
    ring
  rw [hfun, hW.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring
end ReciprocityTheory.L2DbarEstimates
