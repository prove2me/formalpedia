-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_fderiv_chartCutoff_zero_eq_zero_d2cd05d3850b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:32.076647+00:00
-- url     : https://prove2.me/submissions/1c02b892-a526-4b1f-a420-54990a6b3c7d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_sqn_38acd465955c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_zero_eq_1b604a4b9efd

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
theorem _root_.solution {D : ℕ} {x : Fin D → ℂ} (hx : sqn x < 1) :
    fderiv ℝ (chartCutoff 0 : (Fin D → ℂ) → ℝ) x = 0 := by
  have hev : (chartCutoff 0 : (Fin D → ℂ) → ℝ) =ᶠ[nhds x] fun _ => 1 := by
    filter_upwards [(contDiff_sqn.continuous.isOpen_preimage _ isOpen_Iio).mem_nhds hx] with x' hx'
    rw [chartCutoff_zero_eq]
    exact Real.smoothTransition.one_of_one_le (by simp only [Set.mem_preimage, Set.mem_Iio] at hx'; linarith)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
