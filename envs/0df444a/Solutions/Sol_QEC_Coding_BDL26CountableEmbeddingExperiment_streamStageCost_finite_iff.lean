-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_finite_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:21:26.441551+00:00
-- url     : https://prove2.me/submissions/9102ff3e-fadb-4839-ba0f-6f10273e1963

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_nonhalting
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_finite_of_halts

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
    (omega : Omega p) : streamStageCost p i omega < ∞ ↔ streamHalts p i omega := by
  constructor
  · intro hc
    by_contra hh
    rw [streamStageCost_nonhalting p i omega hh] at hc
    exact (lt_irrefl _ hc)
  · exact streamStageCost_finite_of_halts p i omega
end QEC.Coding.BDL26CountableEmbeddingExperiment
