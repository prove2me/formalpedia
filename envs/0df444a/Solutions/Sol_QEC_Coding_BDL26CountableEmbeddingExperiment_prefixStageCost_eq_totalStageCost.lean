-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_eq_totalStageCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:49:34.571865+00:00
-- url     : https://prove2.me/submissions/ed118ebe-ff21-43a4-93aa-73f1e41594a4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_eq_stageCost

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) :
    prefixStageCost p N omega = totalStageCost p N (truncate p N omega) := by
  exact Finset.sum_congr rfl (fun i _ => streamStageCost_eq_stageCost p N i omega)
end QEC.Coding.BDL26CountableEmbeddingExperiment
