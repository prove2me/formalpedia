-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.terminalPotential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:10:41.746174+00:00
-- url     : https://prove2.me/submissions/656a9b60-9e0b-41a2-8912-7bc5d8f66886

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x)
    (zero : baseReadout S n sigma=0) :
    (Data S n).family.coboundary0 0 (terminalPotential S n large sigma e x support zero)=
      (BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word+
        baseComparison S n sigma+baseComparison S n (perturbTop S n sigma e) :=
  Classical.choose_spec (terminal_boundary_exists S n large sigma e x support zero)
end QEC.Coding.BDL26AllDepthBottomComparisonStability
