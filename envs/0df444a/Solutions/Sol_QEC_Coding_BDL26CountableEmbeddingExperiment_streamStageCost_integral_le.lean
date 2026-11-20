-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:20:00.698515+00:00
-- url     : https://prove2.me/submissions/e3e90240-88ae-44a4-9cca-6538ce02fb84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_integral_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_jointStageCost_integral_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (i : ℕ) :
    (∫⁻ omega, streamStageCost p i omega ∂streamLaw p) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p i+1)^10 : ℕ) : ℝ≥0∞) := by
  rw [streamStageCost_integral_eq]
  exact jointStageCost_integral_le p i
end QEC.Coding.BDL26CountableEmbeddingExperiment
