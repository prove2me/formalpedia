-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.measurable_extendedTotalCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:14:50.87318+00:00
-- url     : https://prove2.me/submissions/691fb25b-d16b-4425-aee0-770a8c63eee5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_eq
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_totalMaterializationCost_static
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_totalStageCost
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26ReplacementMaterialization
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (extendedTotalCost p N) := by
  have heq : extendedTotalCost p N = fun z => totalStageCost p N z +
      ((∑ i : Fin N, materializationLabelCost p i.val : ℕ) : ℝ≥0∞) := by
    funext z
    rw [extendedTotalCost_eq,totalMaterializationCost_static]
  rw [heq]
  exact (measurable_totalStageCost p N).add measurable_const
end QEC.Coding.BDL26ReplacementMaterialization
