-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.totalCost_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:36:55.076398+00:00
-- url     : https://prove2.me/submissions/1046ecff-5b2c-4869-8d6c-44306f3f3fd9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_totalCost
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_totalCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_integral_le


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
    (∫⁻ z,totalCost p N z ∂experimentLaw p N)<∞ ∧
    Integrable (fun z => (totalCost p N z).toReal) (experimentLaw p N) := by
  have hf := (totalCost_integral_le p N).trans_lt (ENNReal.natCast_lt_top _)
  refine ⟨hf,?_⟩
  exact integrable_toReal_of_lintegral_ne_top (measurable_totalCost p N).aemeasurable (ne_of_lt hf)
end QEC.Coding.BDL26NativeFiniteComposition
