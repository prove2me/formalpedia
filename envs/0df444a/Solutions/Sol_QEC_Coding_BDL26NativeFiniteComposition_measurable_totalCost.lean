-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.measurable_totalCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:31:41.571797+00:00
-- url     : https://prove2.me/submissions/3201d2a8-52e7-4d95-ba65-ba3debbcdcec

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_sum
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_stageCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_stageCost


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (totalCost p N) := by
  have he : totalCost p N = fun z => ∑ i : Fin N, stageCost p N i z :=
    funext (totalCost_sum p N)
  rw [he]
  exact Finset.measurable_sum _ (fun i hi => measurable_stageCost p N i)
end QEC.Coding.BDL26NativeFiniteComposition
