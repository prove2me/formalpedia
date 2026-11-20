-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalCoordinateTrace.c2_singleton_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:34:53.971293+00:00
-- url     : https://prove2.me/submissions/d9dc91b2-f835-41dd-9fe5-6789439fd29f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_flip_local
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_iff_owner
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_bit_cases
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_scalar_one
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_scalar_singleton
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_scalar_zero
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
theorem _root_.solution (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (r : Physical S 2)
    (hh : hammingSupport (descent S N u q).word ⊆ {r}) :
    levelTwoLocalError S (descent S N u q).word := by
  obtain ⟨c,hc⟩ := BDL26RXQEdgePairTransport.scalar_singleton (descent S N u q).word r hh
  have hraw : (descent S N u q).word=c • (canonicalBasisWord (F:=F) r :
      BDL26LevelTwoLocalBranchEndpoint.Error S) := hc
  rcases BDL26RXQEdgePairTransport.bit_cases c with rfl | rfl
  · have hz : (descent S N u q).word=0 := hraw.trans (BDL26RXQEdgePairTransport.scalar_zero _)
    rw [hz]
    apply (levelTwoLocalError_iff_owner S _).mpr
    refine ⟨BDL26ReplacementSupport.rzCorrectionOwner (RawOne S) S r,?_⟩
    intro t ht
    exact False.elim (ht rfl)
  · have hb : (descent S N u q).word=BDL26FirstZeroEmptySuffix.physicalWord S r := by
      exact (hraw.trans (BDL26RXQEdgePairTransport.scalar_one _)).trans
        (flip_eq_basis S 0 r).symm
    rw [hb]
    exact BDL26FirstZeroEmptySuffix.physical_flip_local S r
end QEC.Coding.BDL26RXPhysicalCoordinateTrace
