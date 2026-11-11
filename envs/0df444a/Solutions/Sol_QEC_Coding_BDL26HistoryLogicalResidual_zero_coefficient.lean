-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.zero_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:57:40.165356+00:00
-- url     : https://prove2.me/submissions/a86ebbd5-26a7-4cca-b007-a5969f0fed5f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_topWord_zero


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n) : topCoefficient S n sigma 0 = 0 := by
  have hw : topCocycle S n sigma 0 = 0 := by
    apply Subtype.ext
    exact topWord_zero S n sigma
  unfold topCoefficient
  rw [hw,map_zero,map_zero]
end QEC.Coding.BDL26HistoryLogicalResidual
