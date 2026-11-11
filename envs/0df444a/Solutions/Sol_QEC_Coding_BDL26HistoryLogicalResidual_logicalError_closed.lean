-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.logicalError_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:47:43.033041+00:00
-- url     : https://prove2.me/submissions/be36681b-163c-4a16-8f2d-a189b1829f85

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution :
    (SuffixData S n).family.coboundary1 (TopIndex n) (logicalError S n) = 0 := by
  rw [suffix_delta1]
  exact (BDL26RZCohomology.mem_cocycle_iff _ _).mp (FC.generator S (n+2) 1).property
end QEC.Coding.BDL26HistoryLogicalResidual
