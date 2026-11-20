-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonResponse.logical_word_nonboundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:21:34.739032+00:00
-- url     : https://prove2.me/submissions/6bff2205-a6f6-4a7a-89c4-413a26fbdd2e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_logicalError_closed
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_logicalError_not_boundary
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_topWord_of_closed
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonResponse
theorem _root_.solution (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    logicalError S n ∉ boundaries S n := by
  intro h
  apply logicalError_not_boundary S n sigma
  obtain ⟨p,hp⟩ := h
  exact ⟨p,hp.trans (topWord_of_closed S n sigma _ (logicalError_closed S n)).symm⟩
end QEC.Coding.BDL26LocalBackgroundComparisonResponse
