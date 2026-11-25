-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_eq_re_5c0d10ff2de2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:16.194019+00:00
-- url     : https://prove2.me/submissions/e6da9a04-d3db-4090-854a-4a6c0bc0c598

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_ReciprocityTheory_AnForm_A_sum_leviC_mul
import Theorems.Thm_ReciprocityTheory_AnForm_hessC_eq_leviC
import Theorems.Thm_ReciprocityTheory_AnForm_sum_mul_leviC


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
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
theorem _root_.solution (φ : (Fin e → ℂ) → ℝ) (z ξ : Fin e → ℂ) :
    levi φ z ξ = (star (star ξ) ⬝ᵥ (hessC φ z *ᵥ star ξ)).re := by
  have key : star (star ξ) ⬝ᵥ (hessC φ z *ᵥ star ξ) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star (star ξ)) (star (star ξ)) := by
    simp only [dotProduct, mulVec, hessC_eq_leviC, sum_leviC_mul]
    exact sum_mul_leviC _ _ _
  rw [key, star_star]
  simp [leviC, levi]
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
