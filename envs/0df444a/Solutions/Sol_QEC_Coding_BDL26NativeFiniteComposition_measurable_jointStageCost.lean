-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.measurable_jointStageCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:37:52.972564+00:00
-- url     : https://prove2.me/submissions/4ef72083-483c-4524-89d6-6ef068f3b954

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_measurable_operationCost
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stageQuery_cost
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


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
namespace QEC.Coding.BDL26NativeFiniteComposition
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (jointStageCost p n) := by
  have he : jointStageCost p n = fun z =>
      Paid.operationCost _ n (canonicalRows _ n z.1) (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) z.2+(deterministicCost p n : ℝ≥0∞) :=
    funext (fun z => stageQuery_cost p n z.1 z.2)
  rw [he]
  exact (Paid.measurable_operationCost _ n (radius_nonneg p) p.lambda
    ((6*p.m+2)*p.lambda)).add measurable_const
end QEC.Coding.BDL26NativeFiniteComposition
