-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonResponse.residual_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:26:49.299005+00:00
-- url     : https://prove2.me/submissions/887fc30a-62f0-4d63-9184-2fae55dade83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonResponse
theorem _root_.solution (S : OddScale) (n : Nat) (sigma : TopInput S n) (a b : W S n) :
    BDL26AllDepthBottomComparisonStability.residual S n sigma (a+b)=
      BDL26AllDepthBottomComparisonStability.residual S n sigma a+BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma a) b := by
  unfold BDL26AllDepthBottomComparisonStability.residual
  rw [BDL26NonzeroBackgroundComparisonStability.perturb_add]
  have h := word_add_self (BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n sigma a))
  symm
  calc
    _ = ((a+b)+BDL26AllDepthBottomComparisonStability.correction S n sigma+
        BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n sigma (a+b)))+
        (BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n sigma a)+
          BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n sigma a)) := by abel
    _ = _ := by rw [h,add_zero]
end QEC.Coding.BDL26LocalBackgroundComparisonResponse
