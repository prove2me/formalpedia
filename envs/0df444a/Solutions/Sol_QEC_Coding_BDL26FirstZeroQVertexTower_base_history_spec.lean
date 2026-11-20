-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroQVertexTower.base_history_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:16:26.439432+00:00
-- url     : https://prove2.me/submissions/e6be1c9b-4257-43b3-92b1-aadaf79a2644

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_first_base_original_D
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_second_base_original_D
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_terminal_syndrome
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoState_eq_pair
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26FirstZeroQVertexTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
section RX
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val%2=0)
variable (q : (state S i.val).presentation.Q)
variable (a b : BDL26RXErrorPullback.Upper S depth i)
variable (he : hammingSupport (a+b) ⊆
  (BDL26RXDecoderAdapter.rxLq S depth i h).correctionRegion q)
include he
end RX
section FixedDepth
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
end FixedDepth
private theorem coboundary0_heq {U V : TannerSquarePresentation} (e : U=V) :
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) := by
  cases e
  rfl
private theorem actual_delta0 (S : OddScale) :
    (tannerCoboundary0 (state S 2).presentation : Potential S →ₗ[F] Error S)=boundary S :=
  eq_of_heq (coboundary0_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26FirstZeroQVertexTower
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroQVertexTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroQVertexTower
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    (SuffixData S n).family.coboundary0 0 (basePotential S n u q t)=
      (descent S n u q).word+
        (actualBase S n).decode (actualInputs S n (input S n u) 0)+
        (actualBase S n).decode
          (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0) := by
  have hp : boundary S (basePotential S n u q t)=
      terminalWord S n u q+D S 0+D S (delta S (terminalWord S n u q)) :=
    Classical.choose_spec (terminal_endpoint S n u q t)
  have hd : delta S (terminalWord S n u q)=secondReadout S n u q :=
    BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs
  have hdecode := congrArg (D S) hd
  have hnormalized := congrArg
    (fun d : Error S => terminalWord S n u q+D S 0+d) hdecode
  have hp' := hp.trans hnormalized
  have hfirst : (actualBase S n).decode (actualInputs S n (input S n u) 0)=D S 0 :=
    (first_base_original_D S n u).trans (congrArg (D S) hs)
  have hsecond : (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)=
        D S (secondReadout S n u q) := second_base_original_D S n u q
  let h : Error S := terminalWord S n u q
  have hcalls := congrArg₂ (fun a b : Error S => h+a+b) hfirst.symm hsecond.symm
  have hbase : (SuffixData S n).family.coboundary0 0 (basePotential S n u q t)=
      boundary S (basePotential S n u q t) := by
    rw [suffix_delta0]
    exact LinearMap.congr_fun (actual_delta0 S) (basePotential S n u q t)
  exact hbase.trans (hp'.trans hcalls)
end QEC.Coding.BDL26FirstZeroQVertexTower
