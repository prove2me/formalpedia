-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:34:14.294497+00:00
-- url     : https://prove2.me/submissions/e803631f-da00-4727-aa6d-6fd655b55da2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearUp_comp
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (a b c : LevelIndex n)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    intervalCocycle S n a c (hab.trans hbc) =
      (intervalCocycle S n b c hbc).comp (intervalCocycle S n a b hab) :=
  linearUp_comp (V := fun i : LevelIndex n => ↥(FC.Cocycle S (i.val+2)))
    (cocycleEdge S n) c.val _ b a hbc hab
end QEC.Coding.BDL26HistoryLogicalResidual
