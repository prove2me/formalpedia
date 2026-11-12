-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.actualStageHalts_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:57:24.117514+00:00
-- url     : https://prove2.me/submissions/65e85887-437e-47ec-b0aa-1aa42b18235c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_inputRows_eq

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
    (z : Experiment p N) : actualStageHalts p N i z ↔ stageHalts p N i z := by
  unfold actualStageHalts stageHalts
  rw [inputRows_eq,incomingRows_points]
end QEC.Coding.BDL26PaidRowsComposition
