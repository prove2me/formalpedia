-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.baseReadout_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:12:01.871825+00:00
-- url     : https://prove2.me/submissions/ed80a701-0bfd-4896-923e-cf7ed35303e9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    baseReadout S n sigma ∈ LinearMap.range
      (tannerCoboundary1 (state S 2).presentation) := by
  obtain ⟨e,he⟩ := (actualInputs S n sigma 0).property
  refine ⟨e,?_⟩
  have heq := LinearMap.congr_fun (suffix_delta1 S n (0 : LevelIndex n)) e
  exact heq.symm.trans he
end QEC.Coding.BDL26AllDepthBottomComparisonStability
