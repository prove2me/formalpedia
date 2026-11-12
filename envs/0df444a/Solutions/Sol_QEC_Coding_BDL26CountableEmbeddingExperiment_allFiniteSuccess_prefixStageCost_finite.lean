-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_prefixStageCost_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:34:23.85605+00:00
-- url     : https://prove2.me/submissions/c6e71020-1f18-40f0-a37f-37b2db0ebc5f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_finite_iff
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_halts


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
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (N : ℕ) :
    prefixStageCost p N omega < ∞ := by
  exact (prefixStageCost_finite_iff p N omega).mpr
    (fun i => allFiniteSuccess_halts p h i.val)
end QEC.Coding.BDL26CountableEmbeddingExperiment
