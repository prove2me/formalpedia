-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonDepth.fixed_scale_small_background_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:21:52.10253+00:00
-- url     : https://prove2.me/submissions/08ae2b53-8c3e-4f7f-826c-bb8a4e82c0a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_small_background_first_zero
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_source_scale_single_flip_stable
import Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_source_scale_single_flip_stable


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth
theorem _root_.solution (S : OddScale) (n B : Nat)
    (large : 33 ≤ S.ell) (deep : 4*B < 2 ^ ((n+1)/2))
    (g : W S n) (small : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g) :=
  BDL26AllDepthBottomComparisonStability.source_scale_single_flip_stable S n large _
    (small_background_first_zero S n B deep g small)
end QEC.Coding.BDL26LocalBackgroundComparisonDepth
