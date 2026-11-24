-- Prove2me | solution 1 for ULHC.besideE_offB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:20:20.566585+00:00
-- url     : https://prove2.me/submissions/fdff006e-3aeb-4f7d-b6c1-24d9d92eaf9a

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_besideB_not_mem
import Theorems.Thm_ULHC_cellJ_add
import Theorems.Thm_ULHC_cellJ_nb_comm
import Theorems.Thm_ULHC_cellJ_zero


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (d : Side) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) {y : Edge}
    (hy : y ∈ cellE (cellJ (nb (cellJ c d (k + 1)) (latB d)) d j)) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by
  intro i hi
  rw [cellJ_nb_comm, cellJ_add] at hy
  exact besideB_not_mem c d (j := 0) (show i < k + 1 + j by omega) (by rw [cellJ_zero]; exact hy)
end ULHC
