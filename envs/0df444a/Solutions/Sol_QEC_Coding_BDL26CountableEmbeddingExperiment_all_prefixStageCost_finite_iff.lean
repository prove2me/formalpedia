-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.all_prefixStageCost_finite_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:34:47.196842+00:00
-- url     : https://prove2.me/submissions/4beb49e8-5f2f-4f1e-b6cd-c4cefd6ad662

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_finite_iff

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    (omega : Omega p) :
    (∀ N, prefixStageCost p N omega < ∞) ↔ ∀ i, streamHalts p i omega := by
  constructor
  · intro h i
    exact (prefixStageCost_finite_iff p (i+1) omega).mp (h (i+1)) (Fin.last i)
  · intro h N
    exact (prefixStageCost_finite_iff p N omega).mpr (fun i => h i.val)
end QEC.Coding.BDL26CountableEmbeddingExperiment
