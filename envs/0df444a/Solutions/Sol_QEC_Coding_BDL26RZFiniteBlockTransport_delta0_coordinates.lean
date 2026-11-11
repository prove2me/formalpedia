-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.delta0_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:37:54.545345+00:00
-- url     : https://prove2.me/submissions/cf01299f-6e49-4d80-aa8e-fcc3061938a5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_reindex_delta0

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
private theorem reindex_delta0 (P U : TannerSquarePresentation) (h : P=U)
    (p : Word BDL26FiniteTannerSquare.Field P.X) :
    reindex (congrArg TannerSquarePresentation.Q h) (tannerCoboundary0 P p)=
      tannerCoboundary0 U (reindex (congrArg TannerSquarePresentation.X h) p) := by
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
theorem _root_.solution (p : Potential S depth i) :
    read1 S depth i odd ((indexedFamily S depth).coboundary0 i.succ p)=
      rzCoboundary0 (Old S depth i) (state S i.val).admissible S (read0 S depth i odd p) := by
  rw [indexedFamily_coboundary0]
  exact reindex_delta0 _ _ (upper_eq S depth i odd) p
end QEC.Coding.BDL26RZFiniteBlockTransport
