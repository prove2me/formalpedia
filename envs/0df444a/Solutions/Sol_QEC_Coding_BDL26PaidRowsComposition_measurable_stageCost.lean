-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.measurable_stageCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:12:35.606016+00:00
-- url     : https://prove2.me/submissions/4f320ef6-1a61-4288-bfd6-f0ba5685e43f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stageCost_eq
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_measurable_rowStageCost
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_stageMaterializationCost_static
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    Measurable (stageCost p N i) := by
  have he : stageCost p N i = fun z => rowStageCost p N i z+
      ((materializationLabelCost p i.val+
        3*Fintype.card (Vertex (StagePresentation p (i.val+1))) : ℕ) : ℝ≥0∞) := by
    funext z
    rw [stageCost_eq,stageMaterializationCost_static]
  rw [he]
  exact (measurable_rowStageCost p N i).add measurable_const
end QEC.Coding.BDL26PaidRowsComposition
