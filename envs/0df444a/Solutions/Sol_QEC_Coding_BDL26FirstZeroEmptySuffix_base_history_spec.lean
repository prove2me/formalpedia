-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.base_history_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:01:47.234192+00:00
-- url     : https://prove2.me/submissions/eb9348af-2651-4817-8447-c95d4a947393

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_empty_descent
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_base_potential_spec
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_syndrome
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_first_base_original_D
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_second_base_original_D
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoState_eq_pair
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
private theorem coboundary0_heq {U V : TannerSquarePresentation} (e : U=V) :
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) := by
  cases e
  rfl
private theorem actual_delta0 (S : OddScale) :
    (tannerCoboundary0 (state S 2).presentation : Potential S →ₗ[F] Error S)=boundary S :=
  eq_of_heq (coboundary0_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26FirstZeroEmptySuffix
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroEmptySuffix
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    (SuffixData S 0).family.coboundary0 0 (elementaryPotential S q)=
      (descent S 0 u q).word+
        (actualBase S 0).decode (actualInputs S 0 (input S 0 u) 0)+
        (actualBase S 0).decode
          (actualInputs S 0 (perturbTop S 0 (input S 0 u) (flip S 0 q)) 0) := by
  have hp := base_potential_spec S q
  rw [second_syndrome S u q hs] at hp
  let h : Error S := (descent S 0 u q).word
  have hflip : (flip S 0 q : Error S)=h := (empty_descent S u q).1.symm
  have hp' := hp.trans
    (congrArg (fun w : Error S => w+D S 0+D S (secondReadout S 0 u q)) hflip)
  have hfirst : (actualBase S 0).decode (actualInputs S 0 (input S 0 u) 0)=D S 0 := by
    have hcall : (actualBase S 0).decode (actualInputs S 0 (input S 0 u) 0)=
        D S (firstReadout S 0 u) := first_base_original_D S 0 u
    exact hcall.trans (congrArg (D S) hs)
  have hsecond : (actualBase S 0).decode
      (actualInputs S 0 (perturbTop S 0 (input S 0 u) (flip S 0 q)) 0)=
        D S (secondReadout S 0 u q) := second_base_original_D S 0 u q
  have hcalls := congrArg₂ (fun a b : Error S => h+a+b) hfirst.symm hsecond.symm
  have hfilled := hp'.trans hcalls
  have hbase : (SuffixData S 0).family.coboundary0 0 (elementaryPotential S q)=
      boundary S (elementaryPotential S q) := by
    rw [suffix_delta0]
    exact LinearMap.congr_fun (actual_delta0 S) (elementaryPotential S q)
  exact hbase.trans hfilled
end QEC.Coding.BDL26FirstZeroEmptySuffix
