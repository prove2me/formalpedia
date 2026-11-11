-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.composed_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:12:35.814842+00:00
-- url     : https://prove2.me/submissions/61f07320-29ff-4160-ab64-8d2b7a5756a8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_adjacent_RX
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_composed_boundary
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_topOutput_eq
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
noncomputable section
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
private theorem full_linear_composition {I J : Type}
    (F : Word BDL26FiniteTannerSquare.Field I →ₗ[BDL26FiniteTannerSquare.Field]
      Word BDL26FiniteTannerSquare.Field J)
    (x c d q : Word BDL26FiniteTannerSquare.Field I)
    (e p r : Word BDL26FiniteTannerSquare.Field J)
    (hx : F x=e+p) (hr : r=p+F q) :
    F (x+c+d+q)=e+F (c+d)+r := by
  rw [map_add,map_add,map_add,map_add,hx,hr]
  abel
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
theorem _root_.solution (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b)
    (p : Potential S (2*j+4) (topStep j))
    (hp : Pullback S (2*j+4) (topStep j) (topStep_odd j)
      (Q0 S (2*j+4) (topStep j) (topStep_odd j) u)
      (Z0 S (2*j+4) (topStep j) (topStep_odd j) u) a b p) :
    ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
      (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))=
      a+b+(topOutput S j a).correction+(topOutput S j b).correction+
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        ((nextOutput S j a).correction+(nextOutput S j b).correction)+
      (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p) := by
  let F : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q →ₗ[
      BDL26FiniteTannerSquare.Field]
      Word BDL26FiniteTannerSquare.Field (state S (2*j+4)).presentation.Q :=
    ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
  let x : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    firstLower S j a b
  let cA : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    (nextOutput S j a).correction
  let cB : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    (nextOutput S j b).correction
  let q : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    (indexedFamily S (2*j+4)).coboundary0 (rxStep j).succ (secondPotential S j u a b)
  let y : Word BDL26FiniteTannerSquare.Field (state S (2*j+3)).presentation.Q :=
    ((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b)
  let e : Word BDL26FiniteTannerSquare.Field (state S (2*j+4)).presentation.Q :=
    updated S (2*j+4) (topStep j) (topStep_odd j) a b
  let dp : Word BDL26FiniteTannerSquare.Field (state S (2*j+4)).presentation.Q :=
    (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p
  let r : Word BDL26FiniteTannerSquare.Field (state S (2*j+4)).presentation.Q :=
    (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p)
  have hX : y=x+cA+cB+q := (adjacent_RX S j u a b he).2.1
  have hF : F y=F (x+cA+cB+q) := congrArg F hX
  have hz : F x=e+dp := hp.1
  have hd : r=dp+F q := composed_boundary S j u a b p
  have ha : F (x+cA+cB+q)=e+F (cA+cB)+r :=
    full_linear_composition F x cA cB q e dp r hz hd
  rw [topOutput_eq,topOutput_eq]
  change F y=e+F (cA+cB)+r
  exact hF.trans ha
end QEC.Coding.BDL26RZPhysicalXStarTransport
