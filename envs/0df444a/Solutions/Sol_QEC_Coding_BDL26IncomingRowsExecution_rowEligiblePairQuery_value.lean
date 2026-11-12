-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowEligiblePairQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:51:57.97668+00:00
-- url     : https://prove2.me/submissions/fa8cce87-fede-4014-92e1-e97e8c46adc0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution

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
    (r : ℝ) (a b : Triangle P) :
    (rowEligiblePairQuery P I r a b).1=(eligiblePairQuery P (statePoints I) r a b).1 :=
  (pair_sim P I r a b).1
end QEC.Coding.BDL26IncomingRowsExecution
