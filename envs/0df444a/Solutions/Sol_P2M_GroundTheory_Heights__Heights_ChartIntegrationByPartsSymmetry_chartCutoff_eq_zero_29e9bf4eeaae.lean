-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_eq_zero_29e9bf4eeaae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:39.457798+00:00
-- url     : https://prove2.me/submissions/4ba022ef-66f7-450b-a9f8-412d8df1fa5b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
theorem _root_.solution {k : ℕ} {y : Fin D → ℂ} (h : 2 * ((k : ℝ) + 1) ^ 2 ≤ ∑ i, ‖y i‖ ^ 2) :
    chartCutoff k y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have : 2 ≤ (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2 := (le_div_iff₀ hk).mpr h
  linarith
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
