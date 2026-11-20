-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.stageCost_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:58:09.36017+00:00
-- url     : https://prove2.me/submissions/b65cae76-5309-4dc3-b0b8-81134b4aedd9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_jointStageCost
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stagePair_law
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stageCost_joint
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_jointStageCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_jointStageCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_jointStageCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePair_law


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
    (∫⁻ z,stageCost p N i z ∂experimentLaw p N) ≤ (stageBudget p i.val : ℝ≥0∞) := by
  rw [stageCost_joint]
  change (∫⁻ z, jointStageCost p i.val (stagePair p N i z) ∂experimentLaw p N) ≤ _
  rw [←lintegral_map (measurable_jointStageCost p i.val)
    (measurable_stagePair p N i),stagePair_law]
  exact jointStageCost_integral_le p i.val
end QEC.Coding.BDL26NativeFiniteComposition
