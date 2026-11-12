-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_integral_eq_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:57:18.130077+00:00
-- url     : https://prove2.me/submissions/5cf9ec71-bf7f-4ab7-8f45-275488157954

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_eq_totalStageCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_law
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_totalStageCost
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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) =
      ∫⁻ z, totalStageCost p N z ∂experimentLaw p N := by
  calc
    _ = ∫⁻ omega, totalStageCost p N (truncate p N omega) ∂streamLaw p := by
      apply lintegral_congr
      exact prefixStageCost_eq_totalStageCost p N
    _ = ∫⁻ z, totalStageCost p N z ∂(streamLaw p).map (truncate p N) :=
      (lintegral_map (measurable_totalStageCost p N) (measurable_truncate p N)).symm
    _ = _ := by rw [truncate_law]
end QEC.Coding.BDL26CountableEmbeddingExperiment
