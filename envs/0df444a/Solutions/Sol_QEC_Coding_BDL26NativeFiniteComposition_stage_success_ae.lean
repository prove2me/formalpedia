-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.stage_success_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:32:37.385877+00:00
-- url     : https://prove2.me/submissions/28a8428f-060e-456c-b934-5867c6b6f02c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stagePair_law
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_outputLaw_good_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_good_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePair_law
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_random_input_geometry_ae


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    ∀ᵐ z ∂experimentLaw p N, stageHalts p N i z ∧ stageGood p N i z := by
  have h := native_random_input_geometry_ae (perturbationOddScale p) i.val p
    (outputLaw p i.val) (outputLaw_good_ae p i.val)
  change ∀ᵐ z ∂(outputLaw p i.val).prod (freshLaw p i.val), _ at h
  rw [←stagePair_law p N i] at h
  filter_upwards [ae_of_ae_map (measurable_stagePair p N i).aemeasurable h] with z hz
  exact ⟨hz.1,hz.2.1⟩
end QEC.Coding.BDL26NativeFiniteComposition
