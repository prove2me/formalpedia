-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.Decoded.prefix_output_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:43:12.524785+00:00
-- url     : https://prove2.me/submissions/0feb0590-220b-42f5-8485-eedfd28a7e99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_prefix
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurePreserving_prefix
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_measurable_prefix
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_measurePreserving_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurePreserving_prefix


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    (experimentLaw p n).map ((evaluate p m) ∘ experimentPrefix p m n h) = outputLaw p m := by
  rw [← Measure.map_map (measurable_evaluate p m) (measurable_prefix p h),
    (measurePreserving_prefix p h).map_eq]
  rfl
end QEC.Coding.BDL26NativeFiniteComposition.Decoded
