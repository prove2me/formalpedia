-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_fderiv_chartCutoff_eq_zero_6171524f7411
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:39.077963+00:00
-- url     : https://prove2.me/submissions/8bf70a4d-e90c-426f-8fe4-5f28ecc9d482

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_eq_one_644a4a0f61f2

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
theorem _root_.solution {k : ℕ} {y : Fin D → ℂ} (h : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2) :
    fderiv ℝ (chartCutoff k) y = 0 := by
  have hc : Continuous fun z : Fin D → ℂ => ∑ i, ‖z i‖ ^ 2 := by fun_prop
  have hopen : IsOpen {z : Fin D → ℂ | ∑ i, ‖z i‖ ^ 2 < ((k : ℝ) + 1) ^ 2} := isOpen_lt hc continuous_const
  have hev : chartCutoff k =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds h] with z hz
    exact chartCutoff_eq_one (le_of_lt hz)
  rw [hev.fderiv_eq]
  simp
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
