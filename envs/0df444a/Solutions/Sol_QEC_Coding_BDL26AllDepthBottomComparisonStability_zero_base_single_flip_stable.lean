-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.zero_base_single_flip_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:52:06.664279+00:00
-- url     : https://prove2.me/submissions/346b126a-5ae7-4d61-9cf4-bac96a1cac8b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_zero_base_full_boundary

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
    (sigma : TopInput S n) (zero : baseReadout S n sigma=0) :
    SingleFlipStable S n sigma := by
  intro q
  exact zero_base_full_boundary S n large sigma (canonicalBasisWord (F:=F) q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q)
    (BDL26LocalizedHistoryErrorDescent.elementary_support S n q) zero
end QEC.Coding.BDL26AllDepthBottomComparisonStability
