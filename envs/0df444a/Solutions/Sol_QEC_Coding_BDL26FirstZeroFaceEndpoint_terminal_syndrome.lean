-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroFaceEndpoint.terminal_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:40:56.235597+00:00
-- url     : https://prove2.me/submissions/195f053d-f22f-4e1a-9452-ebbb4742a5bc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26FirstZeroFaceEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
private theorem actual_delta1 (S : OddScale) :
    (tannerCoboundary1 (state S 2).presentation : Error S →ₗ[F] Syndrome S)=delta S :=
  eq_of_heq (presentation_operations_heq (actual_presentation S)).2.2.2
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26FirstZeroFaceEndpoint
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroFaceEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroFaceEndpoint
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) :
    delta S (descent S n u q).word=secondReadout S n u q := by
  have hd := descent_syndrome S n u q
  rw [suffix_delta1] at hd
  have he := LinearMap.congr_fun (actual_delta1 S) (descent S n u q).word
  have ht : delta S (descent S n u q).word=
      (firstReadout S n u : Syndrome S)+secondReadout S n u q := he.symm.trans hd
  have hs' : (firstReadout S n u : Syndrome S)=0 := hs
  rw [hs',zero_add] at ht
  exact ht
end QEC.Coding.BDL26FirstZeroFaceEndpoint
