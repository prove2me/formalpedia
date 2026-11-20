-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonResponse.residual_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:22:21.231683+00:00
-- url     : https://prove2.me/submissions/16651217-9298-4e96-8fff-b7de2018c433

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonResponse
theorem _root_.solution (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (w : W S n) (closed : (SuffixData S n).family.coboundary1 (TopIndex n) w=0) :
    BDL26AllDepthBottomComparisonStability.residual S n sigma w=w := by
  have same : perturbTop S n sigma w=sigma := by
    apply Subtype.ext
    change sigma.val+((SuffixData S n).family.coboundary1 (TopIndex n)) w=sigma.val
    rw [closed,add_zero]
  rw [BDL26AllDepthBottomComparisonStability.residual,same,add_assoc,word_add_self,add_zero]
end QEC.Coding.BDL26LocalBackgroundComparisonResponse
