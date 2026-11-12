-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.finiteSuccess_handoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:39:18.998102+00:00
-- url     : https://prove2.me/submissions/92002165-4abf-49e7-ba9e-63f1e2532e75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricAvoidance_native_supported_avoidance


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : Experiment p N} (hz : z ∈ finiteSuccess p N) (i : Fin N) :
    IncomingFaceGeometry (StagePresentation p i.val) (perturbationOddScale p)
      (nativePerturbed p i.val (stageInput p N i z) (tableAt p N i z))
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ center, ((familyHits (oldTriangleImage (StagePresentation p i.val)
      (nativePerturbed p i.val (stageInput p N i z) (tableAt p N i z)))
      (Metric.closedBall center 1)).card : ℝ) ≤ triangleDensityBound := by
  have hJ : IsBoundedDensityLocalMap (StagePresentation p i.val) (stageInput p N i z) p.t :=
    hz.2 ⟨i.val,by omega⟩
  exact (BDL26NativeGeometricAvoidance.native_supported_avoidance
    (perturbationOddScale p) i.val (stageInput p N i z) p hJ).2.2 _ (hz.1 i).2
end QEC.Coding.BDL26NativeFiniteComposition
