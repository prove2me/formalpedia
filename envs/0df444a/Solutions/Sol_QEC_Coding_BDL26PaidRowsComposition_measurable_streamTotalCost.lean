-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_streamTotalCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:28:37.251181+00:00
-- url     : https://prove2.me/submissions/ef457d05-cd57-482c-952d-5040fcb89f23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_totalCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_finite_prefix
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
    Measurable (streamTotalCost p N) := by
  have he : streamTotalCost p N = totalCost p N ∘ BDL26CountableEmbeddingExperiment.truncate p N :=
    funext (streamTotalCost_finite_prefix p N)
  rw [he]
  exact (measurable_totalCost p N).comp (BDL26CountableEmbeddingExperiment.measurable_truncate p N)
end QEC.Coding.BDL26PaidRowsComposition
