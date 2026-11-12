-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.Decoded.tableAt_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:45:25.949746+00:00
-- url     : https://prove2.me/submissions/8dc0eb1a-c8ae-4ab6-91c9-ed2a3f8432ac

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_tableAt
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_tableAt_law
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_measurable_tableAt
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_tableAt_law
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_tableAt
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_tableAt_law


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (B : Set (StageTables p i.val)) (hB : MeasurableSet B) :
    experimentLaw p n (tableAt p n i ⁻¹' B) = freshLaw p i.val B := by
  rw [← Measure.map_apply (measurable_tableAt p n i) hB, tableAt_law]
end QEC.Coding.BDL26NativeFiniteComposition.Decoded
