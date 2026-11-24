-- Prove2me | solution 1 for ULHC.pot_jump
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:05.91094+00:00
-- url     : https://prove2.me/submissions/ed58f1a8-6a91-49c2-b859-ed5361214ee2

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
import Theorems.Thm_ULHC_pot_jump_v
import Theorems.Thm_ULHC_pot_jump_h

set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}
namespace ULHC
theorem _root_.solution (hS : Supp E w) (hbal : Balanced w) (e : Edge) :
    pot E w e.hi - pot E w e.lo = w e := by
  obtain ⟨d, p⟩ := e
  cases d
  · exact pot_jump_h hS hbal p
  · exact pot_jump_v hS p
end ULHC
