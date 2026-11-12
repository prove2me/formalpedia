-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_integral_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:22:19.529917+00:00
-- url     : https://prove2.me/submissions/1dde62a7-847a-406d-bef4-bc4d78e08d85

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageCost

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) =
      ∑ i : Fin n, ∫⁻ z, stageCost p n i z ∂experimentLaw p n :=
  lintegral_finsetSum Finset.univ (fun i _ => measurable_stageCost p n i)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
