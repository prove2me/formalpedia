-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.coefficient_eq_iff_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:13:46.077078+00:00
-- url     : https://prove2.me/submissions/b66ce56c-acce-4194-a644-9d7ed730721d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_class_eq_iff_boundary

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (r : Nat) (v w : FC.Cocycle S r) :
    FC.finiteH1Equiv S r (FC.classOf S r v) = FC.finiteH1Equiv S r (FC.classOf S r w) ↔
      ∃ f : Word BDL26Field (state S r).presentation.X,
        tannerCoboundary0 (state S r).presentation f = v.val-w.val := by
  constructor
  · intro h
    exact (class_eq_iff_boundary S r v w).mp ((FC.finiteH1Equiv S r).injective h)
  · intro h
    exact congrArg (FC.finiteH1Equiv S r) ((class_eq_iff_boundary S r v w).mpr h)
end QEC.Coding.BDL26HistoryLogicalResidual
