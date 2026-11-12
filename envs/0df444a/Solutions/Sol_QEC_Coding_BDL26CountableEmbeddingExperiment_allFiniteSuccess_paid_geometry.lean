-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_paid_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:39:31.900345+00:00
-- url     : https://prove2.me/submissions/a7b8b475-02f2-4207-91cc-bc332ab01fb7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_prefixStageCost_finite
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_halts
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_stageFacts


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
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) :
    (∀ i, streamHalts p i omega) ∧
    (∀ N, prefixStageCost p N omega < ∞) ∧
    (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
    ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t :=
  ⟨allFiniteSuccess_halts p h, allFiniteSuccess_prefixStageCost_finite p h,
    allFiniteSuccess_stageFacts p h, allFiniteSuccess_geometry p h⟩
end QEC.Coding.BDL26CountableEmbeddingExperiment
