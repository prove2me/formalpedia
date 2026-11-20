-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.source_even_single_flip_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:00:32.361843+00:00
-- url     : https://prove2.me/submissions/7dc57f95-6e91-4627-8050-a35d80c972ac

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_zero_base_single_flip_stable

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 1≤k)
    (large : 16 ≤ S.half) (sigma : TopInput S (2*(k-1)))
    (zero : baseReadout S (2*(k-1)) sigma=0) :
    2*(k-1)+2=2*k ∧ SingleFlipStable S (2*(k-1)) sigma :=
  ⟨by omega,zero_base_single_flip_stable S _ large sigma zero⟩
end QEC.Coding.BDL26AllDepthBottomComparisonStability
