-- Prove2me | solution 1 for ULHC.back1_cellJ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:35.015048+00:00
-- url     : https://prove2.me/submissions/66782e49-18bf-4a67-93c6-02c81d486c95

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
import Theorems.Thm_ULHC_back1_nb
import Theorems.Thm_ULHC_nb_cellJ


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (j : ℕ) :
    back1 (cellJ c s (j + 1)) s = front1 (cellJ c s j) s := by
  rw [← nb_cellJ, back1_nb]
end ULHC
