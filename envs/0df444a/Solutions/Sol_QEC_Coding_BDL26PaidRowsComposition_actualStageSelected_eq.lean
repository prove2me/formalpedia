-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.actualStageSelected_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:58:13.4223+00:00
-- url     : https://prove2.me/submissions/e927e595-253c-43e9-b6e2-d579c820a248

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_inputRows_eq
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowPrefixQuery_selected


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
    (time : ℕ) (z : Experiment p N) : actualStageSelected p N i time z = stageSelected p N i time z := by
  unfold actualStageSelected stagePrefixRows
  rw [rowPrefixQuery_selected,inputRows_eq,incomingRows_points]
  rfl
end QEC.Coding.BDL26PaidRowsComposition
