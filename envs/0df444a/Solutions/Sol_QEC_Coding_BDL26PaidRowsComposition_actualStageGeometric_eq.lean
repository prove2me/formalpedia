-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.actualStageGeometric_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:04:34.226336+00:00
-- url     : https://prove2.me/submissions/897d3d2c-491f-4740-9c33-7d7cd1c3adfc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stagePrefixRows_rep
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageHaltTime_eq
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_StateRowsRep_points


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
    (z : Experiment p N) : actualStageGeometric p N i z = stageGeometricOutput p N i z := by
  unfold actualStageGeometric
  rw [actualStageHaltTime_eq]
  exact StateRowsRep_points _ _ _ _ (stagePrefixRows_rep p N i (stageHaltTime p N i z) z)
end QEC.Coding.BDL26PaidRowsComposition
