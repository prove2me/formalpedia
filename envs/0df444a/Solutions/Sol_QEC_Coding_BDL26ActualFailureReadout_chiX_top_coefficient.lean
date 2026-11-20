-- Prove2me | solution 1 for QEC.Coding.BDL26ActualFailureReadout.chiX_top_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:50:24.883693+00:00
-- url     : https://prove2.me/submissions/f78f643b-af5e-4a1d-a183-24847e4eac50

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_residual
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_h1Coordinate_eq_pairing


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
    BDL26LogicalDefectProtection.chiX S n u q=
      topCoefficient S n (input S n u) (flip S n q) := by
  change _=BDL26LogicalDefectProtection.h1Coordinate S n
    (topCocycle S n (input S n u) (flip S n q))
  rw [BDL26LogicalDefectProtection.h1Coordinate_eq_pairing]
  change _=wordPairing (topWord S n (input S n u) (flip S n q))
    (BDL26LogicalDefectProtection.zWord S n)
  rw [full_residual]
  rfl
end QEC.Coding.BDL26ActualFailureReadout
