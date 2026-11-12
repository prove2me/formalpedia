-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.paidSuccessorQuery_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:23:29.031843+00:00
-- url     : https://prove2.me/submissions/58005b65-d211-4b46-a7f0-7e27661690a8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_pointRowQuery_map
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_paidSuccessorQuery_rows
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexInputList_complete


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) (v : Vertex (StagePresentation p (n+1))) :
    (pointRowQuery v (paidSuccessorQuery p n J T).1).1 = physicalSuccessorOutput p n J T v := by
  rw [paidSuccessorQuery_rows]
  exact pointRowQuery_map _ v _ (vertexInputList_complete _ v)
end QEC.Coding.BDL26ReplacementMaterialization
