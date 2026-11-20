-- Prove2me | solution 1 for QEC.Coding.BDL26BoundaryTailInvariance.full_potential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:39:42.755798+00:00
-- url     : https://prove2.me/submissions/1ec57422-dc7a-4f4c-a196-1d0dd7beaad8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_base_residual_boundary
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap_commutes0
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_history_equation
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
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n sigma tau top a p hp)=
      top.word+historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma)+
        historyLiftedCorrection (SuffixData S n) (actualHistory S n tau) := by
  unfold fullPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),
    base_residual_boundary S n sigma tau top a p hp]
  exact (history_equation S n sigma tau top).symm
end QEC.Coding.BDL26BoundaryTailInvariance
