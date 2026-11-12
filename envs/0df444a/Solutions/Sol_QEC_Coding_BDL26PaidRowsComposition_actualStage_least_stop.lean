-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.actualStage_least_stop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:42:39.961266+00:00
-- url     : https://prove2.me/submissions/a5fb891a-720d-454a-873b-40ae746e6542

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageSelected_eq
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageHalts_iff
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStageHaltTime_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageSelected_none_iff
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_active_before_haltTime
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_haltTime_spec
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (z : Experiment p N) (h : actualStageHalts p N i z) :
    actualStageSelected p N i (actualStageHaltTime p N i z) z = none ∧
      ∀ time < actualStageHaltTime p N i z, actualStageSelected p N i time z ≠ none := by
  have hh := (actualStageHalts_iff p N i z).mp h
  rw [actualStageHaltTime_eq]
  constructor
  · rw [actualStageSelected_eq]
    apply (stageSelected_none_iff p N i _ z).mpr
    exact haltTime_spec _ _ _ hh
  · intro time ht hn
    have hn' := (stageSelected_none_iff p N i time z).mp
      ((actualStageSelected_eq p N i time z).symm.trans hn)
    obtain ⟨e,he⟩ := active_before_haltTime _ _ _ hh time ht
    rw [hn'] at he
    cases he
end QEC.Coding.BDL26PaidRowsComposition
