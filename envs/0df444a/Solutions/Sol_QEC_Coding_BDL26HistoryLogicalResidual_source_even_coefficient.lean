-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.source_even_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:39:13.874657+00:00
-- url     : https://prove2.me/submissions/e175ce2e-5c76-4928-a308-8fe051758a8a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_equality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (k : Nat) (hk : 1 ≤ k)
    (sigma : (indexedFamily S (2*k)).Syndrome (TopIndex (2*k)))
    (e u : (indexedFamily S (2*k)).Cochain1 (TopIndex (2*k)))
    (hu : (indexedFamily S (2*k)).coboundary1 (TopIndex (2*k)) u = sigma.val) :
    topCoefficient S (2*(k-1)) (sourceEvenInput S k hk sigma) (sourceEvenError S k hk e) =
      lowerCoefficient S (2*(k-1)) (sourceEvenInput S k hk sigma)
        (sourceEvenError S k hk e) (sourceEvenError S k hk u) (source_even_valid S k hk sigma u hu) :=
  coefficient_equality S _ _ _ _ (source_even_valid S k hk sigma u hu)
end QEC.Coding.BDL26HistoryLogicalResidual
