-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowEligiblePairQuery_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:32:08.267489+00:00
-- url     : https://prove2.me/submissions/0d1b2261-2202-47d4-babe-58226d7fe814

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowEligiblePairQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eligiblePairQuery_correct


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton
namespace QEC.Coding.BDL26IncomingRowsExecution
theorem _root_.solution (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (a b : Triangle P) :
    (rowEligiblePairQuery P I r a b).1=true ↔
      triangleColor P a=triangleColor P b ∧ dist (oldAnchor P (statePoints I) a) (oldAnchor P (statePoints I) b)≤r := by
  rw [rowEligiblePairQuery_value]
  exact eligiblePairQuery_correct P (statePoints I) hr a b
end QEC.Coding.BDL26IncomingRowsExecution
