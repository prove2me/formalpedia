-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_fderiv_chartCutoff_le_69838da594e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:22.068706+00:00
-- url     : https://prove2.me/submissions/962cb338-a188-476d-a87a-6d59c61e3810

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_scale_7a59cb9c493b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_chartCutoff_60dfe149687f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
namespace GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
theorem _root_.solution {D : ℕ} (k : ℕ) (y : Fin D → ℂ) :
    ‖fderiv ℝ (chartCutoff k : (Fin D → ℂ) → ℝ) y‖ ≤
      ((k : ℝ) + 1)⁻¹ * ‖fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (((k : ℝ) + 1)⁻¹ • y)‖ := by
  rw [chartCutoff_scale k]
  set c : ℝ := ((k : ℝ) + 1)⁻¹ with hcdef
  have hc : 0 < c := by positivity
  have hd : DifferentiableAt ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (c • y) :=
    (contDiff_chartCutoff 0).differentiable (by norm_num) _
  have hL : HasFDerivAt (fun y : Fin D → ℂ => c • y) (c • ContinuousLinearMap.id ℝ (Fin D → ℂ)) y := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) y).const_smul c
  rw [show (fun y : Fin D → ℂ => chartCutoff 0 (c • y)) = chartCutoff 0 ∘ fun y => c • y from rfl,
    (hd.hasFDerivAt.comp y hL).fderiv]
  calc _ ≤ ‖fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (c • y)‖ * ‖c • ContinuousLinearMap.id ℝ (Fin D → ℂ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) (c • y)‖ * c := by
        gcongr
        rw [norm_smul, Real.norm_of_nonneg hc.le]
        exact mul_le_of_le_one_right hc.le ContinuousLinearMap.norm_id_le
    _ = _ := mul_comm _ _
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
