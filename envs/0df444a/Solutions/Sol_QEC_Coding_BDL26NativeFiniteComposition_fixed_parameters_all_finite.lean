-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.fixed_parameters_all_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:44:46.03868+00:00
-- url     : https://prove2.me/submissions/591ab8db-9d97-4421-afd5-e86dc72eb1b6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_history
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_totalCost
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_integrable
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_finite_on_success
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_history
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_totalCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


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
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N : ℕ,
      Measurable (history p N) ∧ Measurable (totalCost p N) ∧
      (∫⁻ z,totalCost p N z ∂experimentLaw p N) ≤
        (totalCoefficient p*(stageQubits p N+1)^1774 : ℕ) ∧
      Integrable (fun z => (totalCost p N z).toReal) (experimentLaw p N) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ totalCost p N z<∞ ∧
        ∀ i : Fin (N+1), PhysicalGeometry (perturbationOddScale p) i.val (history p N z i) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p,fun N => ⟨measurable_history p N,measurable_totalCost p N,
    totalCost_integral_le p N,(totalCost_integrable p N).2,?_⟩⟩
  filter_upwards [finiteSuccess_ae p N] with z hz
  exact ⟨hz,totalCost_finite_on_success p N z hz,finiteSuccess_geometry p N hz⟩
end QEC.Coding.BDL26NativeFiniteComposition
