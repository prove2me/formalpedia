-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_countedMasterUniverseQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:45:52.321447+00:00
-- url     : https://prove2.me/submissions/ae35b282-c9d6-463c-8583-b2d8970945e9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_filterMapQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_countedMasterCandidateQuery

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
theorem _root_.solution (P : TannerSquarePresentation) (r : ℝ) :
    Measurable (fun J : Vertex P → Space => countedMasterUniverseQuery P J r) := by
  have hraw := measurable_filterMapQuery (fun L J => countedMasterCandidateQuery P J r L)
    (fun L => measurable_countedMasterCandidateQuery P r L)
    (fourTuplesQuery (triangleInputList P)).1
  have hm : Measurable (fun t : List (MasterEvent P) × ℕ =>
      let raw := (t.1, (fourTuplesQuery (triangleInputList P)).2 + t.2)
      let unique := dedupQuery (countedMasterEqQuery P) raw.1
      let sorted := sortQuery (countedMasterCompareQuery P) unique.1
      (sorted.1, raw.2 + unique.2 + sorted.2)) := measurable_of_countable _
  exact hm.comp hraw
end QEC.Coding.BDL26RandomPerturbation
