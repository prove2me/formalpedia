-- Prove2me | solution 1 for ULHC.endCell_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:12.062166+00:00
-- url     : https://prove2.me/submissions/3813a1a5-cf82-498c-87a7-b0093ccadb02

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) : endCell ⟨c, s, k + 2⟩ = cellJ c s (k + 1) := rfl
end ULHC
