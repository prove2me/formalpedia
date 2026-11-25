-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_hermChartPot_of_le_98d5bb553b65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:30.499642+00:00
-- url     : https://prove2.me/submissions/b9c42376-c932-4237-aaa3-f47f6c0823d6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_gbPot_of_le_822a57be635a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_hermChartPot_eq_gbPot_affine_4211beb1f02e


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
theorem _root_.solution (m : ℕ) {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) :
    ContDiff ℝ m (hermChartPot M) := by
  obtain ⟨c, P, κ, hP, hEq⟩ := ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM
  rw [hEq]
  exact ((contDiff_gbPot_of_le m).comp
    (contDiff_const.add (ChartMongeAmpereAffineInvariance.realCLE P hP).contDiff)).add contDiff_const
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
