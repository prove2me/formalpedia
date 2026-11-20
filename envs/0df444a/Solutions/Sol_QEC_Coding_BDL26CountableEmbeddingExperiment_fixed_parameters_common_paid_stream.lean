-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.fixed_parameters_common_paid_stream
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:38.249636+00:00
-- url     : https://prove2.me/submissions/f6143f17-6c13-4bf3-b79b-856cbc3bcb22

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamStageCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_prefixStageCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_common_paid_geometry_ae
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_measure
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurableSet_allFiniteSuccess
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


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
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L,
      (∀ i, Measurable (streamStageCost p i)) ∧
      (∀ N, Measurable (prefixStageCost p N) ∧
        (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) ≤
          ((operationConstant ((6*p.m+2)*p.lambda) *
            (65^10 * (stageQubits p N+1)^11) : ℕ) : ℝ≥0∞)) ∧
      MeasurableSet (allFiniteSuccess p) ∧ streamLaw p (allFiniteSuccess p) = 1 ∧
      ∀ᵐ omega ∂streamLaw p, omega ∈ allFiniteSuccess p ∧
        (∀ i, streamHalts p i omega) ∧
        (∀ N, prefixStageCost p N omega < ∞) ∧
        (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
        ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  exact ⟨p, measurable_streamStageCost p,
    fun N => ⟨measurable_prefixStageCost p N, prefixStageCost_integral_le p N⟩,
    measurableSet_allFiniteSuccess p, allFiniteSuccess_measure p, common_paid_geometry_ae p⟩
end QEC.Coding.BDL26CountableEmbeddingExperiment
