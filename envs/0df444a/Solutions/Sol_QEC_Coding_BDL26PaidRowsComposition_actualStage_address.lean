-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.actualStage_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:41:38.033243+00:00
-- url     : https://prove2.me/submissions/f03ccaa0-bcff-4c70-8928-b90c500e18aa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageCounters_eq
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageSamples_eq

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
    (time : ℕ) (z : Experiment p N) (v : Vertex (StagePresentation p i.val)) :
    (v,actualStageCounters p N i time z v) = (v,stageCounters p N i time z v) ∧
      actualStageSamples p N i time z v = (tableAt p N i z) (v,actualStageCounters p N i time z v) := by
  rw [actualStageCounters_eq,actualStageSamples_eq]
  exact ⟨rfl,rfl⟩
end QEC.Coding.BDL26PaidRowsComposition
