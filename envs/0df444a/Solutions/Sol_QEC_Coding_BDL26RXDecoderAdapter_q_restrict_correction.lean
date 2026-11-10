-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.q_restrict_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:31:37.108229+00:00
-- url     : https://prove2.me/submissions/fe256c42-55e5-4fa7-baba-130ba5e91c23

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
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (RX1 P S)) :
    (wordEquiv (qCorrectionEquiv P S q)).symm
      (restrictWordLinear ((localQ P S).correctionRegion q) w) =
        fun v => w (Sum.inr ⟨q,v⟩) := by
  funext v
  rfl
end QEC.Coding.BDL26RXDecoderAdapter
