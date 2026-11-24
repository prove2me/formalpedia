-- Prove2me | solution 1 for ULHC.besideE_cell0B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:20:50.08669+00:00
-- url     : https://prove2.me/submissions/d1316415-3f88-4849-be0a-f0a23e6a62e1

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_besideB_not_mem
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_shared_unique


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (d : Side) (k : ℕ) {y : Edge}
    (hy : y ∈ cellE (nb (cellJ c d (k + 1)) (latB d))) (hne : y ≠ lat2 (cellJ c d (k + 1)) d) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by
  intro i hi hyi
  by_cases hik : i ≤ k
  · exact besideB_not_mem c d (j := 0) (show i < k + 1 by omega) (by rw [cellJ_zero]; exact hy) hyi
  · obtain rfl : i = k + 1 := by omega
    exact hne ((shared_unique rfl hyi hy).trans (lat2_eq _ _).symm)
end ULHC
