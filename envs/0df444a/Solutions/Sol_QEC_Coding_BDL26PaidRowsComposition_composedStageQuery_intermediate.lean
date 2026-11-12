-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.composedStageQuery_intermediate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:26:36.706948+00:00
-- url     : https://prove2.me/submissions/c45c811a-c02b-405b-88eb-7812e0da8fbb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowExecutionQuery_embedding_rows
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_emittedRows_value


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (rowExecutionQuery (StagePresentation p n) (incomingRows (StagePresentation p n) J)
      (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) T).1 =
      emittedRows p n J T := by
  rw [rowExecutionQuery_embedding_rows,incomingRows_points,emittedRows_value]
end QEC.Coding.BDL26PaidRowsComposition
