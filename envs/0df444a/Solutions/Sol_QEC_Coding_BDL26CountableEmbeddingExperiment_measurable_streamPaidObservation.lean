-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_streamPaidObservation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:37:28.085729+00:00
-- url     : https://prove2.me/submissions/1c156f27-184e-4c6d-a9dc-ccabcfdf572a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamStageCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_prefixStageCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_levelMap


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
    Measurable (streamPaidObservation p N) :=
  (measurable_pi_lambda _ (fun i : Fin (N+1) => measurable_levelMap p i.val)).prodMk
    ((measurable_pi_lambda _ (fun i : Fin N => measurable_streamStageCost p i.val)).prodMk
      (measurable_prefixStageCost p N))
end QEC.Coding.BDL26CountableEmbeddingExperiment
