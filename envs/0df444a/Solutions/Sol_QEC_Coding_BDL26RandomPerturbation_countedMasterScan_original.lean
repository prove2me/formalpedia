-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.countedMasterScan_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:27:56.704964+00:00
-- url     : https://prove2.me/submissions/89a15574-c841-4114-8e90-b4ab6637d0c9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedMasterUniverseQuery_original
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedMasterStateEventQuery_original
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedScan_map_pair

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (R : StateRows P) :
    scanQuery (countedMasterStateEventQuery P J lambda K)
        (countedMasterUniverseQuery P J r).1 R =
      ((actualScanQuery P J r lambda K (eventUniverseQuery P J hr).1 R).1.map
          (eventToMaster P J r),
        (actualScanQuery P J r lambda K (eventUniverseQuery P J hr).1 R).2) := by
  rw [countedMasterUniverseQuery_original P J hr]
  exact countedScan_map_pair (eventToMaster P J r) _ _
    (countedMasterStateEventQuery_original P J r lambda K) _ R
end QEC.Coding.BDL26RandomPerturbation
