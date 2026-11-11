-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_nonhalting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:33:40.73953+00:00
-- url     : https://prove2.me/submissions/3ad462fb-569d-4b74-8819-f02a1f1ff74e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_original

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) (h : ¬ stageHalts p n i z) : stageCost p n i z = ∞ := by
  rw [stageCost_original]
  exact if_neg h
end QEC.Coding.BDL26FiniteEmbeddingExperiment
