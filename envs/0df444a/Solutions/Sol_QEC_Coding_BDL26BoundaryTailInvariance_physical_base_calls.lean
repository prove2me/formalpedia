-- Prove2me | solution 1 for QEC.Coding.BDL26BoundaryTailInvariance.physical_base_calls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:21:28.17002+00:00
-- url     : https://prove2.me/submissions/0fbdf564-792a-4e77-9bd8-a5bc918789e9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_base_calls_eq
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_readouts_eq

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
theorem _root_.solution (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    firstReadout S n u=secondReadout S n u q ∧
      (actualBase S n).decode (actualInputs S n (input S n u) 0)=
        (actualBase S n).decode (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0) ∧
      BDL26LevelTwoDecoder.decode S (firstReadout S n u)=
        BDL26LevelTwoDecoder.decode S (secondReadout S n u q) := by
  have hi := physical_readouts_eq S n u q a p hp 0 (Nat.zero_le _)
  have hv : firstReadout S n u=secondReadout S n u q := congrArg Subtype.val hi
  exact ⟨hv,base_calls_eq S n _ _ (physicalTop S n u q) a p hp,
    congrArg (BDL26LevelTwoDecoder.decode S) hv⟩
end QEC.Coding.BDL26BoundaryTailInvariance
