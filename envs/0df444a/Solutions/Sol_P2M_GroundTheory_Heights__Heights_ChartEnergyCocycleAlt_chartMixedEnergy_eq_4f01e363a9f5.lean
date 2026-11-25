-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_chartMixedEnergy_eq_4f01e363a9f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:42.392632+00:00
-- url     : https://prove2.me/submissions/35b264ac-dabf-4369-85de-292b97e66af6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
theorem _root_.solution (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) :
    chartMixedEnergy X Y k = pairing X Y (fun s : Fin e => if (s : ℕ) < k then X else Y) := by
  unfold chartMixedEnergy pairing dens
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  congr 2
  funext j
  by_cases h : (j : ℕ) < k <;> simp [h]
end GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
