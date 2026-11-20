-- Prove2me | solution 1 for QEC.Coding.BDL26NonzeroBackgroundComparisonStability.terminalPotential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:24:54.698663+00:00
-- url     : https://prove2.me/submissions/06c2c66a-09b1-4d0c-9ca9-a5d203a25f4e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
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
    (Data S n).family.coboundary0 0
      (terminalPotential S n B large sigma0 zero g budget e x support)=
      (BDL26LocalizedHistoryErrorDescent.actualDescent S n (perturbTop S n sigma0 g) e x support 0).word+
        BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n sigma0 g)+
        BDL26AllDepthBottomComparisonStability.baseComparison S n (perturbTop S n (perturbTop S n sigma0 g) e) :=
  Classical.choose_spec (terminal_boundary_exists S n B large sigma0 zero g budget e x support)
end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
