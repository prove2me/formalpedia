-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.delta1_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:17:30.771056+00:00
-- url     : https://prove2.me/submissions/a52176ba-8697-4681-91b0-9689f29cc3a4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_reindex_delta1

section
noncomputable section
namespace QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
namespace Coordinates
variable (P : TannerSquarePresentation) (S : OddScale)
end Coordinates
private theorem reindex_delta1 (P U : TannerSquarePresentation) (h : P=U)
    (w : Word BDL26FiniteTannerSquare.Field P.Q) :
    reindex (congrArg TannerSquarePresentation.Z h) (tannerCoboundary1 P w)=
      tannerCoboundary1 U (reindex (congrArg TannerSquarePresentation.Q h) w) := by
  cases h
  rfl
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
section TopHistory
open BDL26OwnerIncidenceMasks BDL26CanonicalHistoryMarks
end TopHistory
section ConstructorWitness
end ConstructorWitness
end QEC.Coding.BDL26RZFiniteBlockTransport
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
namespace QEC.Coding.BDL26RZFiniteBlockTransport
theorem _root_.solution (w : Upper S depth i) :
    read2 S depth i odd ((indexedFamily S depth).coboundary1 i.succ w)=
      rzCoboundary1 (Old S depth i) (state S i.val).admissible S (read1 S depth i odd w) := by
  rw [indexedFamily_coboundary1]
  exact reindex_delta1 _ _ (upper_eq S depth i odd) w
end QEC.Coding.BDL26RZFiniteBlockTransport
