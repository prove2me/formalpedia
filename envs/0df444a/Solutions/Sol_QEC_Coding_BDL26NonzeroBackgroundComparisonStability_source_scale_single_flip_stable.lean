-- Prove2me | solution 1 for QEC.Coding.BDL26NonzeroBackgroundComparisonStability.source_scale_single_flip_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:13:59.771343+00:00
-- url     : https://prove2.me/submissions/1bc43d44-eacc-46e4-83c0-8ae591177e5f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_single_flip_stable
import Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_threshold_iff
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_threshold_iff
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NonzeroBackgroundComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual (suffix_delta0 suffix_delta1)
open BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26NonzeroBackgroundComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat) (B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n (perturbTop S n sigma0 g) :=
  single_flip_stable S n B ((threshold_iff S B).2 large) sigma0 zero g budget
end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
