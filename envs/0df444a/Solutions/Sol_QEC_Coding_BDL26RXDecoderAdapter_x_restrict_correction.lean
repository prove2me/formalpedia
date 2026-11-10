-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.x_restrict_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:31:21.068712+00:00
-- url     : https://prove2.me/submissions/8814ca35-9a7a-44a3-8046-f4c89cedf878

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (RX1 P S)) :
    (wordEquiv (xCorrectionEquiv P S x)).symm
      (restrictWordLinear ((localX P S).correctionRegion x) w) =
        fun e => w (Sum.inl ⟨x,e⟩) := by
  funext e
  rfl
end QEC.Coding.BDL26RXDecoderAdapter
