-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.rxCode_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:07:11.558987+00:00
-- url     : https://prove2.me/submissions/446b67ba-05d1-48ac-813d-3c2ff64aeb5e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_rxZeroCode_value
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_rxOneCode_value
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_rxTwoCode_value

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
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → Space)
    (v : Vertex (rxReplacementPresentation P S)) : (rxCode P S v).eval J = rxVertexPoint P S J v := by
  cases v with
  | x v => exact rxZeroCode_value P S J v
  | q v => exact rxOneCode_value P S J v
  | z v => exact rxTwoCode_value P S J v
end QEC.Coding.BDL26ReplacementMaterialization
