-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamPaidObservation_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:37:31.354789+00:00
-- url     : https://prove2.me/submissions/75c41df7-737d-4eae-82a4-e08113aeb103

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamPaidObservation_original
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_finitePaidObservation
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_law


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
    (streamLaw p).map (streamPaidObservation p N) =
      (experimentLaw p N).map (finitePaidObservation p N) := by
  have heq : streamPaidObservation p N = finitePaidObservation p N ∘ truncate p N :=
    funext (streamPaidObservation_original p N)
  rw [heq, ← Measure.map_map (measurable_finitePaidObservation p N)
    (measurable_truncate p N), truncate_law]
end QEC.Coding.BDL26CountableEmbeddingExperiment
