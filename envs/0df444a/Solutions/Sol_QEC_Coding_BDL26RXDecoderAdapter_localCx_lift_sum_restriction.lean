-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCx_lift_sum_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:39:26.724943+00:00
-- url     : https://prove2.me/submissions/bd036658-c1f6-42a0-9a09-45a629296152

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_raw_delta0_x
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_sum_at
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_delta0_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (w : ∀ x : P.X, Word BDL26Field (DoubleCylinderVertex P x S)) (x : P.X) :
    restrictWordLinear ((localX P S).correctionRegion x)
      (rxCoboundary0 P S (∑ y : P.X, xLift P S y (w y))) =
        wordLinearMapTranspose (localCx P S x).boundary1 (w x) := by
  funext p
  obtain ⟨e,rfl⟩ := (xCorrectionEquiv P S x).surjective p
  rw [localCx_delta0_apply]
  change rxCoboundary0 P S (∑ y : P.X, xLift P S y (w y)) (Sum.inl ⟨x,e⟩) = _
  rw [raw_delta0_x]
  have hw : (fun v => (∑ y : P.X, xLift P S y (w y)) ⟨x,v⟩) = w x := by
    funext v; exact xLift_sum_at P S w x v
  rw [hw]
end QEC.Coding.BDL26RXDecoderAdapter
