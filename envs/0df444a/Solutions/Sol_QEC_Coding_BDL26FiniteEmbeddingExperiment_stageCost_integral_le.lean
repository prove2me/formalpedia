-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:16:29.635224+00:00
-- url     : https://prove2.me/submissions/2038d348-e48f-4a10-b34e-ecb64c931594

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_integral_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_jointStageCost_integral_le

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (∫⁻ z, stageCost p n i z ∂experimentLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p i.val+1)^10 : ℕ) : ℝ≥0∞) := by
  rw [stageCost_integral_eq]
  exact jointStageCost_integral_le p i.val
end QEC.Coding.BDL26FiniteEmbeddingExperiment
