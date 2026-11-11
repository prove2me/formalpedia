-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.pureX_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:01:19.683304+00:00
-- url     : https://prove2.me/submissions/fbdeaa0e-ef58-4112-895c-84efaad903c7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_mk
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (r : Nat) (v : FC.Cocycle S r) :
    BDL26LogicalQubitPreservation.logicalEquiv S r
        (BDL26LogicalQubitPreservation.logicalClass S r (pureX S r v)) =
      FC.finiteH1Equiv S r (FC.classOf S r v) := by
  rw [BDL26LogicalQubitPreservation.logicalEquiv_mk]
  change FC.finiteH1Equiv S r (FC.classOf S r
    (BDL26LogicalQubitPreservation.cocycleEquiv S r
      ((BDL26LogicalQubitPreservation.cocycleEquiv S r).symm v))) = _
  rw [LinearEquiv.apply_symm_apply]
end QEC.Coding.BDL26HistoryLogicalResidual
