-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_comm_594181c0bc9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:18.106374+00:00
-- url     : https://prove2.me/submissions/1bb969a8-0227-4d5e-ad18-a0b074d9be56

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_hermChartPot_of_le_98d5bb553b65
import Theorems.Thm_ReciprocityTheory_AnForm_A_gradDensSymm_thm


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
theorem _root_.solution {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v w : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    gradDens (fun i => hermChartPot (T i)) v w y = gradDens (fun i => hermChartPot (T i)) w v y :=
  gradDensSymm_thm n _ v w Set.univ isOpen_univ (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn) y
    (Set.mem_univ _)
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
