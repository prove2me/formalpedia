-- Prove2me | solution 1 for QEC.Coding.BDL26BoundaryTailInvariance.base_residual_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:22:54.496176+00:00
-- url     : https://prove2.me/submissions/b61d4600-5cb7-4811-971c-c75451ef95f2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_tail_potential_spec
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_base_calls_eq
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundaryTailInvariance
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26TannerLocalRegularity
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26TransposedStoppedDecoder PauliSymplectic
open scoped Classical
namespace QEC.Coding.BDL26BoundaryTailInvariance
theorem _root_.solution (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word) :
    (SuffixData S n).family.coboundary0 0 (tailPotential S n sigma tau top a p hp 0 (Nat.zero_le _))=
      (path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
        (actualBase S n).decode (actualInputs S n tau 0) := by
  have hc : (path S n sigma tau top 0).word+
      (actualBase S n).decode (actualInputs S n sigma 0)+
      (actualBase S n).decode (actualInputs S n tau 0)=(path S n sigma tau top 0).word := by
    let w : W S n 0 := (path S n sigma tau top 0).word
    let b : W S n 0 := (actualBase S n).decode (actualInputs S n tau 0)
    have he : (actualBase S n).decode (actualInputs S n sigma 0)=b :=
      base_calls_eq S n sigma tau top a p hp
    have hb : b+b=(0 : W S n 0) := word_add_self b
    change (w+(actualBase S n).decode (actualInputs S n sigma 0))+b=w
    exact (congrArg (fun c : W S n 0 => (w+c)+b) he).trans
      ((add_assoc w b b).trans ((congrArg (fun c : W S n 0 => w+c) hb).trans (add_zero w)))
  exact (tail_potential_spec S n sigma tau top a p hp 0 (Nat.zero_le _)).trans hc.symm
end QEC.Coding.BDL26BoundaryTailInvariance
