-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.history_good_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:32:40.938839+00:00
-- url     : https://prove2.me/submissions/bfd74942-bcfe-4bce-bec2-cbfa2b0be97c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_prefix
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_prefix_output_law
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_outputLaw_good_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_good_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_output_law


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin (N+1)) :
    ∀ᵐ z ∂experimentLaw p N,
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p N z i) p.t := by
  have h := outputLaw_good_ae p i.val
  rw [←prefix_output_law p (show i.val ≤ N by omega)] at h
  exact ae_of_ae_map ((measurable_evaluate p i.val).comp
    (measurable_prefix p (show i.val ≤ N by omega))).aemeasurable h
end QEC.Coding.BDL26NativeFiniteComposition
