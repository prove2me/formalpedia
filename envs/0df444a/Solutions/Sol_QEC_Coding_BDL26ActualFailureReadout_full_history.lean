-- Prove2me | solution 1 for QEC.Coding.BDL26ActualFailureReadout.full_history
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:32:44.959508+00:00
-- url     : https://prove2.me/submissions/0bbcef5c-765a-4e7b-941d-f1a1316e259b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_residual
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actual_history


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
    (q : Physical S (n+2)) :
    BDL26LogicalDefectProtection.deltaX S n u q=
      intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        ((descent S n u q).word+
          (actualBase S n).decode (actualInputs S n (input S n u) 0)+
          (actualBase S n).decode
            (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0))+
      (SuffixData S n).family.coboundary0 (TopIndex n) (accumulated S n u q) := by
  have h := BDL26LocalizedHistoryErrorDescent.actual_history S n (input S n u) (flip S n q)
    (BDL26LocalizedHistoryErrorDescent.elementaryCenter S n q) (flip_supported S n q)
  change topWord S n (input S n u) (flip S n q)=_ at h
  rw [full_residual] at h
  exact h
end QEC.Coding.BDL26ActualFailureReadout
