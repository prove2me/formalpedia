-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_streamStageCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:19:08.000627+00:00
-- url     : https://prove2.me/submissions/7110c326-caa1-4b46-bbde-8f9f0ed24378

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_stageCost
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamStageCost_finite_prefix
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageCost


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamStageCost p n) := by
  have he : streamStageCost p n = stageCost p (n+1) (Fin.last n) ∘
      BDL26CountableEmbeddingExperiment.truncate p (n+1) :=
    funext (streamStageCost_finite_prefix p (n+1) (Fin.last n))
  rw [he]
  exact (measurable_stageCost p (n+1) (Fin.last n)).comp
    (BDL26CountableEmbeddingExperiment.measurable_truncate p (n+1))
end QEC.Coding.BDL26PaidRowsComposition
