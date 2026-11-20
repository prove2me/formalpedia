-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:44:46.309044+00:00
-- url     : https://prove2.me/submissions/37b52a4e-e92e-4c00-b7e6-cf947fa5d007

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_le_scaled
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_totalStageCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_integral_le

section
noncomputable section
namespace QEC.Coding.BDL26IncomingRowsExecution
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
private theorem integral_scale_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ≥0∞) (d : ℕ) (hf : Measurable f)
    (h : ∀ z, g z ≤ (d : ℝ≥0∞)*f z) :
    (∫⁻ z, g z ∂μ) ≤ (d : ℝ≥0∞)*(∫⁻ z, f z ∂μ) := by
  calc
    _ ≤ ∫⁻ z, (d : ℝ≥0∞)*f z ∂μ := lintegral_mono h
    _ = _ := lintegral_const_mul _ hf
private theorem degree_twelve_bound (a b : ℝ≥0∞) (C q : ℕ)
    (hpaid : a ≤ ((391*(q+1) : ℕ) : ℝ≥0∞)*b)
    (hold : b ≤ ((C*(65^10*(q+1)^11) : ℕ) : ℝ≥0∞)) :
    a ≤ (((391*C*65^10)*(q+1)^12 : ℕ) : ℝ≥0∞) := by
  calc
    _ ≤ ((391*(q+1) : ℕ) : ℝ≥0∞)*b := hpaid
    _ ≤ ((391*(q+1) : ℕ) : ℝ≥0∞)*((C*(65^10*(q+1)^11) : ℕ) : ℝ≥0∞) := mul_le_mul' le_rfl hold
    _ = _ := by rw [← Nat.cast_mul]; congr 1; ring
end QEC.Coding.BDL26IncomingRowsExecution
end
end

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z, rowTotalCost p N z ∂experimentLaw p N) ≤
      (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10)*(stageQubits p N+1)^12 : ℕ) : ℝ≥0∞) := by
  exact degree_twelve_bound
    (∫⁻ z, rowTotalCost p N z ∂experimentLaw p N)
    (∫⁻ z, totalStageCost p N z ∂experimentLaw p N)
    (operationConstant ((6*p.m+2)*p.lambda)) (stageQubits p N)
    (integral_scale_bound (experimentLaw p N) (totalStageCost p N) (rowTotalCost p N)
      (391*(stageQubits p N+1)) (measurable_totalStageCost p N) (rowTotalCost_le_scaled p N))
    (totalStageCost_integral_le p N)
end QEC.Coding.BDL26IncomingRowsExecution
