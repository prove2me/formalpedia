-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.map2_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:48:49.918591+00:00
-- url     : https://prove2.me/submissions/d43daae9-8111-443b-997c-b2f82b5b2446

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_selected_rz

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
private theorem reindex_output {ι α β : Type} (h : α=β)
    (f : Word BDL26FiniteTannerSquare.Field ι →ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field α)
    (g : Word BDL26FiniteTannerSquare.Field ι →ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field β) (he : HEq f g) (w : Word BDL26FiniteTannerSquare.Field ι) :
    reindex h (f w)=g w := by cases h; rw [eq_of_heq he]; rfl
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
theorem _root_.solution (w : (indexedFamily S depth).Cochain2 i.castSucc) :
    read2 S depth i odd (((indexedDecoderData S depth).selectedMap i).map2 w)=
      map2Coord (Old S depth i) (state S i.val).admissible S w :=
  reindex_output _ _ _ (indexedDecoderData_selected_rz S depth i odd).2.2 w
end QEC.Coding.BDL26RZFiniteBlockTransport
