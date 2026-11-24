-- Prove2me | solution 1 for ULHC.besideE_offA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:19:15.671201+00:00
-- url     : https://prove2.me/submissions/e4238171-890f-467f-978a-30a58a6da690

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_besideA_not_mem
import Theorems.Thm_ULHC_cellJ_add
import Theorems.Thm_ULHC_cellJ_nb_comm
import Theorems.Thm_ULHC_cellJ_zero


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (d : Side) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) {y : Edge}
    (hy : y ∈ cellE (cellJ (nb (cellJ c d (k + 1)) (latA d)) d j)) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by
  intro i hi
  rw [cellJ_nb_comm, cellJ_add] at hy
  exact besideA_not_mem c d (j := 0) (show i < k + 1 + j by omega) (by rw [cellJ_zero]; exact hy)
end ULHC
