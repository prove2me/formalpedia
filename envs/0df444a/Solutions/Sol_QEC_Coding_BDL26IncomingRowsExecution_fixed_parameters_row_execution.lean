-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.fixed_parameters_row_execution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:52:28.968941+00:00
-- url     : https://prove2.me/submissions/a6c8fdba-1df5-45b0-9ab5-5a7d5fd632cf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_measurable_rowTotalCost
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_finite_on_success
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton
namespace QEC.Coding.BDL26IncomingRowsExecution
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N,
      Measurable (rowTotalCost p N) ∧
      (∫⁻ z, rowTotalCost p N z ∂experimentLaw p N) ≤
        (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10)*(stageQubits p N+1)^12 : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ rowTotalCost p N z<∞ := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p,fun N => ⟨measurable_rowTotalCost p N,rowTotalCost_integral_le p N,?_⟩⟩
  filter_upwards [finiteSuccess_ae p N] with z h
  exact ⟨h,rowTotalCost_finite_on_success p N z h⟩
end QEC.Coding.BDL26IncomingRowsExecution
