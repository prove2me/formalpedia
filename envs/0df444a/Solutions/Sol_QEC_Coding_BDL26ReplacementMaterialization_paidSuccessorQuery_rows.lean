-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.paidSuccessorQuery_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:28:08.814418+00:00
-- url     : https://prove2.me/submissions/b4c8c624-9c7e-4ef9-8772-c19f3946f595

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_materializeRows_value

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
    (paidSuccessorQuery p n J T).1 =
      (vertexInputList (StagePresentation p (n+1))).map (fun v => (v,physicalSuccessorOutput p n J T v)) :=
  materializeRows_value p n J T
end QEC.Coding.BDL26ReplacementMaterialization
