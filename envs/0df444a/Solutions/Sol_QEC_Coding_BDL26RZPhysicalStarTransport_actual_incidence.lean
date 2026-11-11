-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.actual_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:39:13.637656+00:00
-- url     : https://prove2.me/submissions/ef8ba753-476f-4575-a388-40ed99e800ff

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
section
noncomputable section
namespace QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
private theorem cast_qz (U V : TannerSquarePresentation) (hp : U=V)
    (q : U.Q) (z : U.Z) :
    U.qz q z=V.qz ((Equiv.cast (congrArg TannerSquarePresentation.Q hp)) q)
      ((Equiv.cast (congrArg TannerSquarePresentation.Z hp)) z) := by
  cases hp
  rfl
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
end QEC.Coding.BDL26RZPhysicalStarTransport
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalStarTransport
theorem _root_.solution (q : FamilyQ S depth i.succ) (u : FamilyZ S depth i.succ) :
    (state S (i.val+1)).presentation.qz q u=
      rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
        (coord1 S depth i odd q) (coord2 S depth i odd u) :=
  cast_qz _ _ (upper_eq S depth i odd) q u
end QEC.Coding.BDL26RZPhysicalStarTransport
