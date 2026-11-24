-- Prove2me | solution 1 for ULHC.endCell_mk2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:07.194526+00:00
-- url     : https://prove2.me/submissions/1ef4875a-5eba-4fe8-9325-110b3e4cd51e

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) : endCell ⟨c, s, k + 2⟩ = cellJ c s (k + 1) := rfl
end ULHC
