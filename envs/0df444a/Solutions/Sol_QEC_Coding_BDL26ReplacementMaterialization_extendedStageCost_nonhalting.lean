-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.extendedStageCost_nonhalting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:22:12.239699+00:00
-- url     : https://prove2.me/submissions/b44d4cb2-bf39-4a09-bada-fcc22f39b8db

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedStageCost_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_nonhalting


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : ¬ stageHalts p N i z) :
    extendedStageCost p N i z = ∞ := by
  rw [extendedStageCost_eq,stageCost_nonhalting p N i z h,top_add]
end QEC.Coding.BDL26ReplacementMaterialization
