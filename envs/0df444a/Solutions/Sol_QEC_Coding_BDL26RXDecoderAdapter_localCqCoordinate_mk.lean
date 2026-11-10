-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCqCoordinate_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:36:39.264133+00:00
-- url     : https://prove2.me/submissions/bcb17793-6098-43b4-8fd3-6e37f1757c69

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (c : (localCq P S q).middleCocycleCode.carrier) :
    localCqCohomologyEquiv P A S q (Submodule.Quotient.mk c) =
      c.1 (qCorrectionEquiv P S q (0, Sum.inl (Sum.inl ()))) := by
  change rxCqH1Coordinate P q S
    (Submodule.Quotient.mk ((reindexForward (rxCq P q S) (Equiv.refl _)
      (qCorrectionEquiv P S q) (qSyndromeEquiv P S q)).mapMiddleCocycle c)) = _
  rw [rxCqH1Coordinate_mk]
  change wordLinearMapTranspose (wordEquiv (qCorrectionEquiv P S q)).toLinearMap
    c.1 (0, Sum.inl (Sum.inl ())) = _
  rw [transpose_wordEquiv]
  rfl
end QEC.Coding.BDL26RXDecoderAdapter
