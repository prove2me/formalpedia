-- Prove2me | solution 1 for QEC.Coding.BDL26ActualFailureReadout.chiX_lower_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:04:53.484178+00:00
-- url     : https://prove2.me/submissions/41770475-b57e-48fd-9a8e-1c14f2c3ce05

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_chiX_top_coefficient
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_equality
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (q : Physical S (n+2)) (a : (SuffixData S n).family.Cochain1 (TopIndex n))
    (ha : (SuffixData S n).family.coboundary1 (TopIndex n) a=(input S n u).val) :
    BDL26LogicalDefectProtection.chiX S n u q=
      lowerCoefficient S n (input S n u) (flip S n q) a ha :=
  (chiX_top_coefficient S n u q).trans
    (coefficient_equality S n (input S n u) (flip S n q) a ha)
end QEC.Coding.BDL26ActualFailureReadout
