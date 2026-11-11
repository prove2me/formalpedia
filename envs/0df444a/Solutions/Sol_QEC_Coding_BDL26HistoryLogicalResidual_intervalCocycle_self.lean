-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:56:48.34827+00:00
-- url     : https://prove2.me/submissions/261b6205-c1ee-4ea9-972f-28418718b9be

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearUp_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (a : LevelIndex n) :
    intervalCocycle S n a a (Nat.le_refl _) = LinearMap.id :=
  linearUp_self (V := fun i : LevelIndex n => ↥(FC.Cocycle S (i.val+2)))
    (cocycleEdge S n) a.val _
end QEC.Coding.BDL26HistoryLogicalResidual
