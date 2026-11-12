-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:34:01.320247+00:00
-- url     : https://prove2.me/submissions/f3e026a4-5825-4a9d-94ae-227db5f879ae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost

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
    (omega : Omega p) :
    streamStageCost p i omega = actualExecutionCost (StagePresentation p i)
      (levelMap p omega i) (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) (omega i) := rfl
end QEC.Coding.BDL26CountableEmbeddingExperiment
