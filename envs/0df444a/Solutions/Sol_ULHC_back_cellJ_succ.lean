-- Prove2me | solution 1 for ULHC.back_cellJ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:45.5663+00:00
-- url     : https://prove2.me/submissions/cb4925d4-880d-47f8-9875-7a058bbc1575

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_nb_cellJ


set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (j : ℕ) : back (cellJ c s (j + 1)) s = front (cellJ c s j) s := by
  rw [← nb_cellJ, back_nb]
end ULHC
