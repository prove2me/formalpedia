-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCx_global_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:35:15.946218+00:00
-- url     : https://prove2.me/submissions/4b27d5b0-d9ca-4a5d-9192-5acd2b50f1fb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_x_restrict_correction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_raw_x_restriction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_delta1_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S)) (x : P.X) :
    restrictWordLinear ((localX P S).syndromeRegion x) (rxCoboundary1 P S w) =
      wordLinearMapTranspose (localCx P S x).boundary2
        (restrictWordLinear ((localX P S).correctionRegion x) w) := by
  funext p
  obtain ⟨f,rfl⟩ := (xSyndromeEquiv P S x).surjective p
  rw [localCx_delta1_apply, x_restrict_correction]
  exact raw_x_restriction P S w x f
end QEC.Coding.BDL26RXDecoderAdapter
