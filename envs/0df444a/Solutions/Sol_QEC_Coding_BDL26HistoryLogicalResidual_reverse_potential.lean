-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.reverse_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:38:37.693666+00:00
-- url     : https://prove2.me/submissions/146d8229-7c77-4b56-9480-4ca798fc281a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_boundary_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (ftop : (SuffixData S n).family.Cochain0 (TopIndex n))
    (hftop : (SuffixData S n).family.coboundary0 (TopIndex n) ftop = topWord S n sigma e) :
    ∃ f2 : (SuffixData S n).family.Cochain0 0,
      (SuffixData S n).family.coboundary0 0 f2 = lowerWord S n sigma e u :=
  (boundary_iff S n sigma e u hu).mp ⟨ftop,hftop⟩
end QEC.Coding.BDL26HistoryLogicalResidual
