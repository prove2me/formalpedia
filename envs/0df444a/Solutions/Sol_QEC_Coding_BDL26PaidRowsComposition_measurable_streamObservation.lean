-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_streamObservation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:48:57.483265+00:00
-- url     : https://prove2.me/submissions/c7550dc2-ac44-43c3-bb04-f324150b0a65

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_finiteObservation
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamObservation_finite
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26PaidRowsComposition
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (streamObservation p N) := by
  have he : streamObservation p N = finiteObservation p N ∘ BDL26CountableEmbeddingExperiment.truncate p N :=
    funext (streamObservation_finite p N)
  rw [he]
  exact (measurable_finiteObservation p N).comp (BDL26CountableEmbeddingExperiment.measurable_truncate p N)
end QEC.Coding.BDL26PaidRowsComposition
