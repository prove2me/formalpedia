-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:03:36.940612+00:00
-- url     : https://prove2.me/submissions/831f0ab2-7a30-403f-92a7-a24b5fcd5bca

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearUp_succ


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (a : LevelIndex n) (i : StepIndex n) (hai : a.val ≤ i.val) :
    intervalCocycle S n a i.succ (by change a.val ≤ i.val+1; omega) =
      (cocycleEdge S n i).comp (intervalCocycle S n a i.castSucc hai) :=
  linearUp_succ (V := fun j : LevelIndex n => ↥(FC.Cocycle S (j.val+2)))
    (cocycleEdge S n) i.val (Nat.le_of_lt_succ i.succ.isLt) a hai
end QEC.Coding.BDL26HistoryLogicalResidual
