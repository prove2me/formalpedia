-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.Decoded.measurable_stagePair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:35:25.132857+00:00
-- url     : https://prove2.me/submissions/fe118358-b35a-458b-a5b8-3fe047da774e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_tableAt
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_stageInput
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_measurable_tableAt
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_measurable_stageInput
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageInput
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_tableAt


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeFiniteComposition
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric BDL26KeyedGeometricExecution BDL26NativeKeyExecutionBridge
open BDL26NativeGeometricExecution BDL26NativeGeometricExecutionCost
open BDL26NativeGeometricScanCost BDL26NativeGeometricJointExecution
open BDL26ReplacementMaterialization BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
open QEC.Coding.BDL26NativeFiniteComposition.Decoded
namespace QEC.Coding.BDL26NativeFiniteComposition.Decoded
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (stagePair p n i) :=
  (measurable_stageInput p n i).prodMk (measurable_tableAt p n i)
end QEC.Coding.BDL26NativeFiniteComposition.Decoded
