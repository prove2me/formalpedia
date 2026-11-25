-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_scale_7a59cb9c493b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:28.652802+00:00
-- url     : https://prove2.me/submissions/d2ae0551-fcdb-4a88-a681-3c9812a42b11

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_smul_7b55cce31069
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_eq_86e7091cfeb0
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
theorem _root_.solution {D : ℕ} (k : ℕ) :
    (chartCutoff k : (Fin D → ℂ) → ℝ) = fun y => chartCutoff 0 (((k : ℝ) + 1)⁻¹ • y) := by
  funext y
  rw [chartCutoff_eq, chartCutoff_zero_eq, sqn_smul, inv_pow]
  congr 1
  ring
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
