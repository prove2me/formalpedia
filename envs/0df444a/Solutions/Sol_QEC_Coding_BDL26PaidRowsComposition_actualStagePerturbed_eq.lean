-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.actualStagePerturbed_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:59:14.135231+00:00
-- url     : https://prove2.me/submissions/5c2aa997-fe7f-4f45-82f8-41d1f6547c38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stampRowsQuery_canonical
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_inputRows_eq
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowExecutionQuery_embedding_rows


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
    (z : Experiment p N) : actualStagePerturbed p N i z = stagePerturbedOutput p N i z := by
  unfold actualStagePerturbed
  rw [inputRows_eq,rowExecutionQuery_embedding_rows,incomingRows_points,
    stampRowsQuery_canonical,incomingRows_points]
  rfl
end QEC.Coding.BDL26PaidRowsComposition
