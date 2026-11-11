-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.actual_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:34:28.294952+00:00
-- url     : https://prove2.me/submissions/e8f76a98-1e46-45d5-88c0-353aea25e459

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
section
noncomputable section
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
private theorem cast_xq (U V : TannerSquarePresentation) (hp : U=V)
    (x : U.X) (q : U.Q) : U.xq x q=
      V.xq ((Equiv.cast (congrArg TannerSquarePresentation.X hp)) x)
        ((Equiv.cast (congrArg TannerSquarePresentation.Q hp)) q) := by
  cases hp
  rfl
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
section HistoryBridge
open BDL26HistorySyndromeSensitivity
end HistoryBridge
section Adjacent
end Adjacent
end QEC.Coding.BDL26RZPhysicalXStarTransport
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
theorem _root_.solution (u : FamilyX S depth i.succ) (r : FamilyQ S depth i.succ) :
    (state S (i.val+1)).presentation.xq u r=
      rzXQIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
        (coord0 S depth i odd u) (coord1 S depth i odd r) :=
  cast_xq _ _ (upper_eq S depth i odd) u r
end QEC.Coding.BDL26RZPhysicalXStarTransport
