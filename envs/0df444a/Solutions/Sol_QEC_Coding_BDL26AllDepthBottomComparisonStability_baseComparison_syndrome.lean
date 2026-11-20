-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.baseComparison_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:20:44.775186+00:00
-- url     : https://prove2.me/submissions/989cf6dc-de4a-4417-ad99-8cfd9567d999

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_baseReadout_valid
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_rightInverse
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    (Data S n).family.coboundary1 0 (baseComparison S n sigma) =
      (actualInputs S n sigma 0).val := by
  rw [suffix_delta1]
  exact BDL26BottomLocalFirstMinWeightComparison.comparison_rightInverse
    S (baseReadout S n sigma) (baseReadout_valid S n sigma)
end QEC.Coding.BDL26AllDepthBottomComparisonStability
