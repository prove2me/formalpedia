-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.vertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:25:33.859555+00:00
-- url     : https://prove2.me/submissions/0c6af508-6ead-4f32-9e38-a09b6efb93b6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) :
    Fintype.card (Vertex P) = Fintype.card P.X+Fintype.card P.Q+Fintype.card P.Z := by
  rw [Fintype.card_congr (vertexSumEquiv P),Fintype.card_sum,Fintype.card_sum]
  omega
end QEC.Coding.BDL26RandomPerturbation
