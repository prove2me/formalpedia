-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:34:31.725014+00:00
-- url     : https://prove2.me/submissions/05c1386f-4af5-46ad-b79b-529ee1759a86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_eq_stageCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_prefix
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {M N : ℕ}
    (h : M ≤ N) (i : Fin M) (omega : Omega p) :
    stageCost p M i (experimentPrefix p M N h (truncate p N omega)) =
      streamStageCost p (i.castLE h).val omega := by
  rw [stageCost_prefix]
  exact (streamStageCost_eq_stageCost p N (i.castLE h) omega).symm
end QEC.Coding.BDL26CountableEmbeddingExperiment
