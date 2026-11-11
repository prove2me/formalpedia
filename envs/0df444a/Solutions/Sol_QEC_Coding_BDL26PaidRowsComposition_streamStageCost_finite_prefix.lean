-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.streamStageCost_finite_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:40:38.084634+00:00
-- url     : https://prove2.me/submissions/fbd69793-7009-4aea-9469-1cb59f29f75d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamRun_truncate
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_tableAt_truncate
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
    streamStageCost p i.val omega = stageCost p N i (BDL26CountableEmbeddingExperiment.truncate p N omega) := by
  unfold streamStageCost stageCost inputRows
  rw [BDL26CountableEmbeddingExperiment.truncate_prefix,
    BDL26CountableEmbeddingExperiment.tableAt_truncate,streamRun_truncate]
end QEC.Coding.BDL26PaidRowsComposition
