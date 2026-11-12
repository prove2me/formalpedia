-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.nonhalting_default_and_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:36:15.829024+00:00
-- url     : https://prove2.me/submissions/a8e92723-c6b0-4ec0-aff4-a08743cf82c7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_nonhalting
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamHaltTime_of_not_halts


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) (h : ¬ streamHalts p i omega) :
    streamHaltTime p i omega = 0 ∧ streamStageCost p i omega = ∞ :=
  ⟨streamHaltTime_of_not_halts p i omega h, streamStageCost_nonhalting p i omega h⟩
end QEC.Coding.BDL26CountableEmbeddingExperiment
