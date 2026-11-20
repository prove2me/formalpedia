-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.nonboundary_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:14:44.027941+00:00
-- url     : https://prove2.me/submissions/6322d483-6b57-4680-9b73-443f9cd6305e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_residual_restriction
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
theorem _root_.solution (sigma0 : TopInput S n) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n sigma0 (backgroundRestriction S n g
        (queryMask S n sigma0 g (canonicalBasisWord (F:=BDL26Field) q))))
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by
  rwa [← residual_restriction S n sigma0 g (canonicalBasisWord (F:=BDL26Field) q)]
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
