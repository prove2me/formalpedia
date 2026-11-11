-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.perturbTop_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:01:55.84918+00:00
-- url     : https://prove2.me/submissions/7ed02814-c8bf-4e48-a91f-bbd0ab335b26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n))
    (he : (SuffixData S n).family.coboundary1 (TopIndex n) e = 0) :
    perturbTop S n sigma e = sigma := by
  apply Subtype.ext
  change sigma.val + (SuffixData S n).family.coboundary1 (TopIndex n) e = sigma.val
  rw [he,add_zero]
end QEC.Coding.BDL26HistoryLogicalResidual
