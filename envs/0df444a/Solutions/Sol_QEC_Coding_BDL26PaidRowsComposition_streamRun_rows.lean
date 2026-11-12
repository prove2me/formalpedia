-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.streamRun_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:43:24.136548+00:00
-- url     : https://prove2.me/submissions/03bb7439-83b3-4d34-8c19-eec89986d26d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_run_rows
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamRun_truncate

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) (N : ℕ) :
    (streamRun p omega N).1 = incomingRows (StagePresentation p N)
      (BDL26CountableEmbeddingExperiment.levelMap p omega N) := by
  rw [streamRun_truncate,run_rows]
  rfl
end QEC.Coding.BDL26PaidRowsComposition
