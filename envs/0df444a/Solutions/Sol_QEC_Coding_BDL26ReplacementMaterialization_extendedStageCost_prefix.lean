-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.extendedStageCost_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:24:09.57317+00:00
-- url     : https://prove2.me/submissions/e21fe0cb-2e29-4fd9-8671-e7ca13d8ba84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedStageCost_eq
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_stageMaterializationCost_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_prefix


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {M N : ℕ}
    (h : M ≤ N) (i : Fin M) (z : Experiment p N) :
    extendedStageCost p M i (experimentPrefix p M N h z) = extendedStageCost p N (i.castLE h) z := by
  rw [extendedStageCost_eq,extendedStageCost_eq,stageCost_prefix,stageMaterializationCost_prefix]
end QEC.Coding.BDL26ReplacementMaterialization
