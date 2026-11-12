-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_nonhalting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:35:01.061204+00:00
-- url     : https://prove2.me/submissions/debf57b0-9d7e-47c8-ace6-44cf54025b47

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_nonhalting
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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {i N : ℕ}
    (hi : i < N) (omega : Omega p) (h : ¬ streamHalts p i omega) :
    prefixStageCost p N omega = ∞ := by
  apply top_unique
  have hb := streamStageCost_le_prefix p N ⟨i,hi⟩ omega
  rw [streamStageCost_nonhalting p i omega h] at hb
  exact hb
end QEC.Coding.BDL26CountableEmbeddingExperiment
