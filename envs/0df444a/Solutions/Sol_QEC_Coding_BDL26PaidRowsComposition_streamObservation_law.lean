-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.streamObservation_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:45:23.813282+00:00
-- url     : https://prove2.me/submissions/04e6e68e-dd50-41ae-9932-3caf5001e0ae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_finiteObservation_original
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_finiteObservation
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamObservation_finite
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_law


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
    (BDL26CountableEmbeddingExperiment.streamLaw p).map (streamObservation p N) =
      (experimentLaw p N).map (originalObservation p N) := by
  have he : streamObservation p N = finiteObservation p N ∘ BDL26CountableEmbeddingExperiment.truncate p N :=
    funext (streamObservation_finite p N)
  rw [he,← Measure.map_map (measurable_finiteObservation p N)
    (BDL26CountableEmbeddingExperiment.measurable_truncate p N),BDL26CountableEmbeddingExperiment.truncate_law]
  have ho : finiteObservation p N = originalObservation p N := funext (finiteObservation_original p N)
  rw [ho]
end QEC.Coding.BDL26PaidRowsComposition
