-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.qSubdivisionCode_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:12:35.274664+00:00
-- url     : https://prove2.me/submissions/11577607-9a86-4ff0-97e5-8975e1f38186

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
    (q : P.Q) (v : QSubdivisionVertex P q S) :
    (qSubdivisionCode P S q v).reads ≤ 2 ∧ (qSubdivisionCode P S q v).work ≤ 48 := by
  rcases v with (v | e) | ⟨e,i⟩ <;>
    norm_num [qSubdivisionCode,blendCode,PointCode.reads,PointCode.work,
      contractionExpr,stepExpr,RealExpr.cost]
end QEC.Coding.BDL26ReplacementMaterialization
