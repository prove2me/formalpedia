-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.lowerError_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:22:53.817067+00:00
-- url     : https://prove2.me/submissions/3691600f-cfd0-434b-b6b4-9c3fbd20c0f9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzData_coordinates

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
private theorem reindex_input {ι α β : Type} (h : α=β)
    (f : Word BDL26FiniteTannerSquare.Field α →ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field ι)
    (g : Word BDL26FiniteTannerSquare.Field β →ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field ι) (he : HEq f g) (w : Word BDL26FiniteTannerSquare.Field α) :
    f w=g (reindex h w) := by cases h; rw [eq_of_heq he]; rfl
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
theorem _root_.solution (a b : Upper S depth i) :
    lowerError S depth i odd a b=rzQParity (Old S depth i) S (read1 S depth i odd (a+b)) :=
  reindex_input _ _ _ (rzData_coordinates S depth i odd).2.2.2 _
end QEC.Coding.BDL26RZFiniteBlockTransport
