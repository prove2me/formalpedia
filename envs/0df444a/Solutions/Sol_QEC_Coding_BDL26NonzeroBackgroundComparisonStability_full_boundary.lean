-- Prove2me | solution 1 for QEC.Coding.BDL26NonzeroBackgroundComparisonStability.full_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:55:51.86346+00:00
-- url     : https://prove2.me/submissions/28de076c-6157-43ee-9476-2ae542c76ad0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_topPotential_spec
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_topPotential_spec
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_topPotential_spec
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
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) e ∈
      LinearMap.range ((Data S n).family.coboundary0 (TopIndex n)) :=
  ⟨topPotential S n B large sigma0 zero g budget e x support,
    topPotential_spec S n B large sigma0 zero g budget e x support⟩
end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
