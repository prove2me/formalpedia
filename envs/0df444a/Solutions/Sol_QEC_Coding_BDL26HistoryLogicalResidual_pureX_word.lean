-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.pureX_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:36:10.192201+00:00
-- url     : https://prove2.me/submissions/baa41dcf-e4d4-4262-9f06-1745f99f5f63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_cocycleEquiv_symm_word


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (r : Nat) (v : FC.Cocycle S r) : (pureX S r v).val = v.val :=
  BDL26LogicalQubitPreservation.cocycleEquiv_symm_word S r v
end QEC.Coding.BDL26HistoryLogicalResidual
