-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_mono_2f4f957da48a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:54.318092+00:00
-- url     : https://prove2.me/submissions/75644ea1-ef54-4b66-a238-374e4e773cd4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_apply_1aabed1ce02b

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
theorem _root_.solution (y : Fin D → ℂ) : Monotone fun k : ℕ => chartCutoff k y := by
  intro a b hab
  simp only [chartCutoff_apply]
  apply Real.smoothTransition.monotone
  have hab' : ((a : ℝ) + 1) ^ 2 ≤ ((b : ℝ) + 1) ^ 2 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    gcongr
  have hs : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
  have := div_le_div_of_nonneg_left hs (by positivity) hab'
  linarith
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
