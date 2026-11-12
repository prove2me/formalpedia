-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.evaluate_decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:36:34.319318+00:00
-- url     : https://prove2.me/submissions/a341a002-d609-4657-b8b9-25c44899b63b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_nativeOutput_decoded


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    evaluate p N z=Decoded.evaluate p N (decodeExperiment p N z) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change successor p N (evaluate p N z.1) z.2 =
      Decoded.successor p N (Decoded.evaluate p N (decodeExperiment p N z.1))
        (decodedTable (perturbationOddScale p) N z.2)
    rw [←ih]
    unfold successor nativePerturbed Decoded.successor
    rw [nativeOutput_decoded]
end QEC.Coding.BDL26NativeFiniteComposition
