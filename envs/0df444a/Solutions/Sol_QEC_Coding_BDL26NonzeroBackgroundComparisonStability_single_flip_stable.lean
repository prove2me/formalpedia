-- Prove2me | solution 1 for QEC.Coding.BDL26NonzeroBackgroundComparisonStability.single_flip_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:03:58.630889+00:00
-- url     : https://prove2.me/submissions/226f7240-ba40-4d3f-8e34-bb0c1f6f522b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_full_boundary
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
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n (perturbTop S n sigma0 g) := by
  intro q
  exact full_boundary S n B large sigma0 zero g budget (canonicalBasisWord (F:=F) q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (BDL26LocalizedHistoryErrorDescent.elementary_support S n q)
end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
