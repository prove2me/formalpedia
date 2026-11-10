-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCq_global_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:34:55.937202+00:00
-- url     : https://prove2.me/submissions/3b58b10f-ccd1-4e80-aa2d-ec03422134ce

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_q_restrict_correction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_delta1_apply
import Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_rxCoboundary1_q_of_x_restrictions_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S))
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w = 0) (q : P.Q) :
    restrictWordLinear ((localQ P S).syndromeRegion q) (rxCoboundary1 P S w) =
      wordLinearMapTranspose (localCq P S q).boundary2
        (restrictWordLinear ((localQ P S).correctionRegion q) w) := by
  funext p
  obtain ⟨e,rfl⟩ := (qSyndromeEquiv P S q).surjective p
  rw [localCq_delta1_apply, q_restrict_correction]
  exact rxCoboundary1_q_of_x_restrictions_zero P S w hx q e
end QEC.Coding.BDL26RXDecoderAdapter
