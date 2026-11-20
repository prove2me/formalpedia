-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonDepth.comparison_residual_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:44:51.800187+00:00
-- url     : https://prove2.me/submissions/720a02d0-14c3-42a9-90f7-7127e9f5797c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_correction_syndrome
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth
theorem _root_.solution (S : OddScale) (n : Nat)
    (sigma : TopInput S n) (e : W S n) :
    (SuffixData S n).family.coboundary1 (TopIndex n)
      (BDL26AllDepthBottomComparisonStability.residual S n sigma e)=0 := by
  have first := BDL26AllDepthBottomComparisonStability.correction_syndrome S n sigma
  have second := BDL26AllDepthBottomComparisonStability.correction_syndrome S n (perturbTop S n sigma e)
  unfold BDL26AllDepthBottomComparisonStability.residual
  rw [map_add,map_add,first,second]
  change (SuffixData S n).family.coboundary1 (TopIndex n) e+sigma.val+
    (sigma.val+(SuffixData S n).family.coboundary1 (TopIndex n) e)=0
  calc
    _ = ((SuffixData S n).family.coboundary1 (TopIndex n) e+
        (SuffixData S n).family.coboundary1 (TopIndex n) e)+(sigma.val+sigma.val) := by abel
    _ = 0 := by rw [word_add_self,word_add_self,add_zero]
end QEC.Coding.BDL26LocalBackgroundComparisonDepth
