-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.source_scale_single_flip_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:00:29.102899+00:00
-- url     : https://prove2.me/submissions/d14311ba-300c-4391-8aa5-2bfced93955f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_zero_base_single_flip_stable
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_threshold_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat) (large : 33≤S.ell)
    (sigma : TopInput S n) (zero : baseReadout S n sigma=0) :
    SingleFlipStable S n sigma :=
  zero_base_single_flip_stable S n ((threshold_iff S).2 large) sigma zero
end QEC.Coding.BDL26AllDepthBottomComparisonStability
