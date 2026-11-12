-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.streamStageTrace_finite_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:37:11.453387+00:00
-- url     : https://prove2.me/submissions/3fb690ba-1f09-4ba6-8c73-1dae6293a819

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stageTrace_prefix
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamStageTrace_last
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_prefix


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamStageTrace p i.val omega = stageTrace p N i (BDL26CountableEmbeddingExperiment.truncate p N omega) := by
  rcases i with ⟨i,hi⟩
  rw [streamStageTrace_last]
  have h := stageTrace_prefix p hi (Fin.last i)
    (BDL26CountableEmbeddingExperiment.truncate p N omega)
  rw [BDL26CountableEmbeddingExperiment.truncate_prefix] at h
  exact h
end QEC.Coding.BDL26PaidRowsComposition
