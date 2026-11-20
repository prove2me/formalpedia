-- Prove2me | solution 1 for QEC.Coding.BDL26ActualFailureReadout.topPotential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:51:14.946077+00:00
-- url     : https://prove2.me/submissions/2a3d59a7-69dc-4a10-84ef-5ae95a3e7236

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_history
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_basePotential_spec
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap_commutes0
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualBase_decode_zero
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26ActualFailureReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian
open scoped Classical BigOperators
private theorem first_base_zero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (hs : firstReadout S n u=0) :
    (actualBase S n).decode (actualInputs S n (input S n u) 0)=0 := by
  have hi : actualInputs S n (input S n u) 0=0 := Subtype.ext hs
  rw [hi,actualBase_decode_zero]
private theorem second_base_zero (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (ht : secondReadout S n u q=0) :
    (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)=0 := by
  have hi : actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0=0 :=
    Subtype.ext ht
  rw [hi,actualBase_decode_zero]
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26ActualFailureReadout
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ActualFailureReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26ActualFailureReadout
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (hs : firstReadout S n u=0) (ht : secondReadout S n u q=0) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (topPotential S n u q hs ht)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  unfold topPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),basePotential_spec]
  have h := full_history S n u q
  rw [first_base_zero S n u hs,second_base_zero S n u q ht,add_zero,add_zero] at h
  exact h.symm
end QEC.Coding.BDL26ActualFailureReadout
