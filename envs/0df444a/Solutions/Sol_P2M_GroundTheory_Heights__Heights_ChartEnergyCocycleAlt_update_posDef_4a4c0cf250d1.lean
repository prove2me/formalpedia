-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_update_posDef_4a4c0cf250d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:19.917854+00:00
-- url     : https://prove2.me/submissions/3fc3318b-c241-4c1c-86ef-7922af1904f2

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
theorem _root_.solution {T : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hT : ∀ j, (T j).PosDef) (p : Fin e)
    {X : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (s : Fin e) : (Function.update T p X s).PosDef := by
  rw [Function.update_apply]
  split_ifs
  exacts [hX, hT s]
end GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
