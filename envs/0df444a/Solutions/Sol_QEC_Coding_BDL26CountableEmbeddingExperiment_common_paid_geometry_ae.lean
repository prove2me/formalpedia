-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.common_paid_geometry_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:38:49.710591+00:00
-- url     : https://prove2.me/submissions/9d35cc66-e983-46af-8a7d-ddc037f002d4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_paid_geometry
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_ae


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    ∀ᵐ omega ∂streamLaw p, omega ∈ allFiniteSuccess p ∧
      (∀ i, streamHalts p i omega) ∧
      (∀ N, prefixStageCost p N omega < ∞) ∧
      (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t := by
  filter_upwards [allFiniteSuccess_ae p] with omega h
  exact ⟨h, allFiniteSuccess_paid_geometry p h⟩
end QEC.Coding.BDL26CountableEmbeddingExperiment
