-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_kern_analyticAt_of_mem_f25be706a099
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:33.727252+00:00
-- url     : https://prove2.me/submissions/1138429b-3e9e-4cdc-8ae2-c4aa2c7902da

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_sub_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
namespace GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
theorem _root_.solution {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) {z : Fin n → ℂ}
    (hz : z ∈ ball c r) : AnalyticAt ℂ (kern c r) z := by
  refine Finset.analyticAt_fun_prod _ fun i _ => ?_
  set u := cubeCoord c r i - z i • (1 : C(Cube n, ℂ))
  have hu : IsUnit u := (ContinuousMap.isUnit_iff_forall_ne_zero u).mpr fun θ' => by
    simp only [u, cubeCoord, ContinuousMap.sub_apply, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact torusMap_sub_ne hr hz θ'.1 i
  have hA : AnalyticAt ℂ (fun w : Fin n → ℂ => cubeCoord c r i - w i • (1 : C(Cube n, ℂ))) z := by
    have h := (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i) (1 : C(Cube n, ℂ))).analyticAt z
    exact analyticAt_const.sub h
  exact (analyticAt_inverse (𝕜 := ℂ) hu.unit).comp_of_eq hA (by simp [u])
end GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
