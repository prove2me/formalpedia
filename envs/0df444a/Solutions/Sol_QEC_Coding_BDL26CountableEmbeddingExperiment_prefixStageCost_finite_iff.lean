-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_finite_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:26:58.661276+00:00
-- url     : https://prove2.me/submissions/e3cf9c63-490f-4cb4-8f2f-2d79965e4b1f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_finite_of_halts
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_finite_iff
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_le_prefix

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
    prefixStageCost p N omega < ∞ ↔ ∀ i : Fin N, streamHalts p i.val omega := by
  constructor
  · intro h i
    exact (streamStageCost_finite_iff p i.val omega).mp
      (lt_of_le_of_lt (streamStageCost_le_prefix p N i omega) h)
  · intro h
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact streamStageCost_finite_of_halts p i.val omega (h i)
end QEC.Coding.BDL26CountableEmbeddingExperiment
