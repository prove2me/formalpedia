-- Prove2me | solution 1 for ULHC.rev_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:14:47.636267+00:00
-- url     : https://prove2.me/submissions/83f794ec-537c-4ba3-88c4-5ebe19cd764c

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
import Theorems.Thm_ULHC_nOn_rev
import Theorems.Thm_ULHC_mem_flipCol


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (F : Finset Edge) (c : Pt) (s : Side) (k : ℕ) :
    flipCol (flipCol F c s (k + 2)) (cellJ c s (k + 1)) s.opp (k + 2) = F := by
  ext x
  rw [mem_flipCol, mem_flipCol, nOn_rev]
  tauto
end ULHC
