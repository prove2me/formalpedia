-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.decodeExperiment_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:18:29.071341+00:00
-- url     : https://prove2.me/submissions/f145db1f-1890-43d8-8d49-654ef4011555

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_decodeExperiment
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_decoded_table_law
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_decodeTable


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
    (experimentLaw p N).map (decodeExperiment p N)=Decoded.experimentLaw p N := by
  induction N with
  | zero => exact Measure.map_dirac' measurable_const ()
  | succ N ih =>
    have h := Measure.map_prod_map (experimentLaw p N) (freshLaw p N)
      (measurable_decodeExperiment p N)
      (Resampling.VariableRelabeling.measurable_decodeTable (SR.decode (perturbationOddScale p) N))
    change ((experimentLaw p N).map (decodeExperiment p N)).prod
      ((freshLaw p N).map (decodedTable (perturbationOddScale p) N)) =
      ((experimentLaw p N).prod (freshLaw p N)).map
        (Prod.map (decodeExperiment p N) (decodedTable (perturbationOddScale p) N)) at h
    change ((experimentLaw p N).prod (freshLaw p N)).map
      (Prod.map (decodeExperiment p N) (decodedTable (perturbationOddScale p) N)) =
        (Decoded.experimentLaw p N).prod (Decoded.freshLaw p N)
    rw [←h,ih]
    change (Decoded.experimentLaw p N).prod
      ((nativeTableMeasure (perturbationOddScale p) N p).map (decodedTable _ N)) = _
    rw [decoded_table_law]
    rfl
end QEC.Coding.BDL26NativeFiniteComposition
