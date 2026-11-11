-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stageQubits_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:58:42.798232+00:00
-- url     : https://prove2.me/submissions/0db9325b-f741-4f4b-bb6b-d046399d24db

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageQubits_double

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    Monotone (stageQubits p) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := stageQubits_double p n
  omega
end QEC.Coding.BDL26FiniteEmbeddingExperiment
