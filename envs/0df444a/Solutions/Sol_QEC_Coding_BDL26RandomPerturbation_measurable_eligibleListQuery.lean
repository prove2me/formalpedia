-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_eligibleListQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:33:40.649198+00:00
-- url     : https://prove2.me/submissions/b1e12e1c-9b73-4e62-9b62-d5a6ddd2d927

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAllQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_eligiblePairQuery

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (r : ℝ)
    (L : List (Triangle P)) :
    Measurable (fun J : Vertex P → Space =>
      ((eligibleListQuery P J r L).1.2, (eligibleListQuery P J r L).2)) := by
  let unique := dedupQuery (triangleLabelEqQuery P) L
  have hp : Measurable (fun J : Vertex P → Space =>
      listAllQuery (fun a => listAllQuery (eligiblePairQuery P J r a) unique.1) unique.1) :=
    measurable_listAllQuery _ (fun a => measurable_listAllQuery _
      (fun b => measurable_eligiblePairQuery P r a b) unique.1) unique.1
  exact (measurable_of_countable (fun t : Bool × ℕ =>
    (decide (unique.1.length = 4) && t.1, unique.2 + t.2 + unique.1.length + 2))).comp hp
end QEC.Coding.BDL26RandomPerturbation
