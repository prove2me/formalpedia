-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_cons_hermChartPot_48972275ef2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:52:00.265886+00:00
-- url     : https://prove2.me/submissions/2351c096-ffa1-4d5f-8cbe-2918c3080f6c

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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
theorem _root_.solution (C : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) :
    (fun j => hermChartPot ((Fin.cons C T : Fin (n + 1) → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) j)) =
      (Fin.cons (hermChartPot C) fun i => hermChartPot (T i) : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
