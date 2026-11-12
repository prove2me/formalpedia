-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_streamStageTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:35:42.182564+00:00
-- url     : https://prove2.me/submissions/4c500edd-6947-4c60-a523-4b4e0716a438

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_stageTrace
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamStageTrace_last
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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamStageTrace p n) := by
  have he : streamStageTrace p n = stageTrace p (n+1) (Fin.last n) ∘
      BDL26CountableEmbeddingExperiment.truncate p (n+1) := funext (streamStageTrace_last p n)
  rw [he]
  exact (measurable_stageTrace p (n+1) (Fin.last n)).comp
    (BDL26CountableEmbeddingExperiment.measurable_truncate p (n+1))
end QEC.Coding.BDL26PaidRowsComposition
