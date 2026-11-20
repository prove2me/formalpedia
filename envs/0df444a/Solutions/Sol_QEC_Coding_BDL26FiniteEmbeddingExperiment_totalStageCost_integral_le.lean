-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:37:45.384662+00:00
-- url     : https://prove2.me/submissions/846d3b40-3916-4a0a-a8e1-f2b220f3707b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stage_size_sum_le
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_integral_le_sum
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) *
        (65^10 * (stageQubits p n+1)^11) : ℕ) : ℝ≥0∞) := by
  exact (totalStageCost_integral_le_sum p n).trans
    ((Nat.cast_le (α := ℝ≥0∞)).mpr
      (Nat.mul_le_mul_left _ (stage_size_sum_le p n)))
end QEC.Coding.BDL26FiniteEmbeddingExperiment
