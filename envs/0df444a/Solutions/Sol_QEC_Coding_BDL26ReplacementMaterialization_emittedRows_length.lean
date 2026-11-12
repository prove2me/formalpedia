-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.emittedRows_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:41:46.519236+00:00
-- url     : https://prove2.me/submissions/b0c74aa4-dfb6-43fe-b566-d08e3e9db706

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_emittedRows_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexInputList_length


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
    (J : StageMaps p n) (T : StageTables p n) :
    (emittedRows p n J T).length = Fintype.card (Vertex (StagePresentation p n)) := by
  rw [emittedRows_value,List.length_map,vertexInputList_length]
end QEC.Coding.BDL26ReplacementMaterialization
