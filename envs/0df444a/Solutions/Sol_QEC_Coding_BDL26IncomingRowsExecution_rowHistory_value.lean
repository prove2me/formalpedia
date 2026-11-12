-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowHistory_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:44:32.847201+00:00
-- url     : https://prove2.me/submissions/6d19c1c3-e2ac-4e83-9f16-2f3fae82e095

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowEvaluate_value

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowHistory p N z=history p N z := by
  funext i
  exact rowEvaluate_value p i.val _
end QEC.Coding.BDL26IncomingRowsExecution
