-- Prove2me | solution 1 for ULHC.beside_end_farB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:04:13.902437+00:00
-- url     : https://prove2.me/submissions/9fcdf8bd-b559-4e57-be3f-cb9599011b35

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_besideB_not_mem
import Theorems.Thm_ULHC_cellJ_nb_comm
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_add
import Theorems.Thm_ULHC_cellJ_zero


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) {n : ℕ} (hn : 2 ≤ n) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s (k + 1)) (latB s)) s (n - 1))) :
    ∀ j < k + 2, x ∉ cellE (cellJ c s j) := by
  intro j hj
  rw [cellJ_nb_comm, cellJ_add] at hx
  exact besideB_not_mem c s (j := 0) (show j < k + 1 + (n - 1) by omega) (by rw [cellJ_zero]; exact hx)
end ULHC
