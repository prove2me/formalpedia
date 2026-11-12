-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.starCode_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:40:48.500306+00:00
-- url     : https://prove2.me/submissions/172bf37a-37c2-41cd-919d-d846b9182d90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization

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
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (v : XStarVertex P x) :
    (starCode P S x v).reads ≤ 2 ∧ (starCode P S x v).work ≤ 40 := by
  norm_num [starCode,blendCode,PointCode.reads,PointCode.work,contractionExpr,RealExpr.cost]
end QEC.Coding.BDL26ReplacementMaterialization
