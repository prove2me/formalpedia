-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.actualStage_nonhalting_default
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:42:51.818318+00:00
-- url     : https://prove2.me/submissions/e5e432e7-b503-44cb-8379-faa9399d4c88

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stageCost_nonhalting
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageHalts_iff
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageHaltTime_eq
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageGeometric_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_nonhalting
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageGeometricOutput_of_not_halts
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageHaltTime_of_not_halts
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (z : Experiment p N) (h : ¬actualStageHalts p N i z) :
    actualStageHaltTime p N i z = 0 ∧
      actualStageGeometric p N i z = assignment (tableAt p N i z) (fun _ => 0) ∧
      stageCost p N i z = ∞ := by
  have hh : ¬stageHalts p N i z := fun ha => h ((actualStageHalts_iff p N i z).mpr ha)
  exact ⟨(actualStageHaltTime_eq p N i z).trans (stageHaltTime_of_not_halts p N i z hh),
    (actualStageGeometric_eq p N i z).trans (stageGeometricOutput_of_not_halts p N i z hh),
    stageCost_nonhalting p N i z hh⟩
end QEC.Coding.BDL26PaidRowsComposition
