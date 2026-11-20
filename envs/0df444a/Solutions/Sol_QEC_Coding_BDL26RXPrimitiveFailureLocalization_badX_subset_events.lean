-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.badX_subset_events
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:16:11.103075+00:00
-- url     : https://prove2.me/submissions/b00933fd-e4b5-4a71-9716-6a5aa65e0e63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_mem_primitiveEvent
import Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_badX_first_zero_localized
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_mem_firstEvent


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXPrimitiveFailureLocalization
theorem _root_.solution (S : OddScale) (N : Nat) :
    BDL26LogicalDefectProtection.badX S N ⊆
      BDL26LocalSearchFailureReduction.firstEvent S N ∪ primitiveEvent S N := by
  intro u hu
  by_cases hs : firstReadout S N u=0
  · obtain ⟨q,b,hb,p,hpos,hodd,hc,hp,hw⟩ := badX_first_zero_localized S N u hu hs
    exact Finset.mem_union.mpr (Or.inr ((mem_primitiveEvent S N u).mpr ⟨hs,q,b,hb,p,hp,hw⟩))
  · exact Finset.mem_union.mpr
      (Or.inl ((BDL26LocalSearchFailureReduction.mem_firstEvent S N u).mpr hs))
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
