-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonResponse.restricted_background_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:27:12.877223+00:00
-- url     : https://prove2.me/submissions/f7ead3c1-9d7d-4ebd-a757-b11fed2b26a2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_source_scale_single_flip_stable
import Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_source_scale_single_flip_stable


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonResponse
theorem _root_.solution (S : OddScale) (n B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : W S n) (A : Finset (Q S n))
    (small : HammingWeight (backgroundRestriction S n g A) ≤ B) (q : Q S n) :
    BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 (backgroundRestriction S n g A))
      (canonicalBasisWord (F:=BDL26Field) q) ∈ boundaries S n :=
  BDL26NonzeroBackgroundComparisonStability.source_scale_single_flip_stable S n B large sigma0 zero _ small q
end QEC.Coding.BDL26LocalBackgroundComparisonResponse
