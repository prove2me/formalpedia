-- Prove2me | solution 1 for ULHC.rev_cellJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:10:41.623802+00:00
-- url     : https://prove2.me/submissions/53dda091-6219-4f8d-b16b-a1de39594c1d

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
import Theorems.Thm_ULHC_rev_cellJ_add
import Theorems.Thm_ULHC_NoTypeIII_at


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) {i k : ℕ} (hi : i ≤ k + 1) :
    cellJ (cellJ c s (k + 1)) s.opp i = cellJ c s (k + 1 - i) := by
  have := rev_cellJ_add c s i (k + 1 - i)
  rwa [show i + (k + 1 - i) = k + 1 by omega] at this
end ULHC
