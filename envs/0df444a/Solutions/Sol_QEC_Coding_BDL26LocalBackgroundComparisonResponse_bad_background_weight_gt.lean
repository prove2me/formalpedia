-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonResponse.bad_background_weight_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:22:02.746855+00:00
-- url     : https://prove2.me/submissions/80299e65-d98a-44fd-8454-89ffc432f7c1

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
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0)
    (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) : B < HammingWeight g := by
  by_contra small
  apply bad
  exact BDL26NonzeroBackgroundComparisonStability.source_scale_single_flip_stable
    S n B large sigma0 zero g (by omega) q
end QEC.Coding.BDL26LocalBackgroundComparisonResponse
