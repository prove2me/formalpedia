-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_tendsto_chartCutoff_a7c11729e7ae
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:56.352796+00:00
-- url     : https://prove2.me/submissions/bf586a91-3e75-4f00-9353-33c3f611cb06

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
theorem _root_.solution (y : Fin D → ℂ) : Tendsto (fun k : ℕ => chartCutoff k y) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.sqrt (∑ i, ‖y i‖ ^ 2))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  symm
  apply chartCutoff_eq_one
  have h0 : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
  have hs : Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ (k : ℝ) + 1 := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  calc ∑ i, ‖y i‖ ^ 2 = Real.sqrt (∑ i, ‖y i‖ ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ ((k : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
