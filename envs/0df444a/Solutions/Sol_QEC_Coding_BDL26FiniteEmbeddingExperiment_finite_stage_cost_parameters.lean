-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.finite_stage_cost_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:45:08.45057+00:00
-- url     : https://prove2.me/submissions/2d112256-2eb1-4589-a206-ce6e91835ace

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_totalStageCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_and_totalStageCost_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ n : ℕ,
      Measurable (totalStageCost p n) ∧
      (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) ≤
        ((operationConstant ((6*p.m+2)*p.lambda) *
          (65^10 * (stageQubits p n+1)^11) : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n ∧ totalStageCost p n z < ∞ := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  exact ⟨p, fun n => ⟨measurable_totalStageCost p n, totalStageCost_integral_le p n,
    finiteSuccess_and_totalStageCost_ae p n⟩⟩
end QEC.Coding.BDL26FiniteEmbeddingExperiment
