-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.first_zero_original_snapshot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:07:23.074436+00:00
-- url     : https://prove2.me/submissions/91a3564a-1178-4485-a76c-8496270d81f3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_first_zero_primitive
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_snapshot_original


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
theorem _root_.solution (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    ∃ (b : Nat) (hb : b≤N) (p : Primitive S b), parse S N q=.primitive p ∧
      (actualDescent S N (input S N u) (flip S N q) (elementaryCenter S N q)
        (BDL26BoundaryTailInvariance.physical_supported S N q) ⟨b,Nat.lt_succ_of_le hb⟩).word=
          canonicalBasisWord (F:=F) p.physical := by
  obtain ⟨b,hb,p,hp,hw⟩ := first_zero_primitive S N u q hs hc
  refine ⟨b,hb,p,hp,?_⟩
  rw [← BDL26BoundaryTailInvariance.snapshot_original]
  exact hw
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
