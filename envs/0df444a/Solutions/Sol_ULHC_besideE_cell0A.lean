-- Prove2me | solution 1 for ULHC.besideE_cell0A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:20:35.413794+00:00
-- url     : https://prove2.me/submissions/c38417e9-7525-443f-9dc2-fe406c4e59bf

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_besideA_not_mem
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_shared_unique


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (d : Side) (k : ℕ) {y : Edge}
    (hy : y ∈ cellE (nb (cellJ c d (k + 1)) (latA d))) (hne : y ≠ lat1 (cellJ c d (k + 1)) d) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by
  intro i hi hyi
  by_cases hik : i ≤ k
  · exact besideA_not_mem c d (j := 0) (show i < k + 1 by omega) (by rw [cellJ_zero]; exact hy) hyi
  · obtain rfl : i = k + 1 := by omega
    exact hne ((shared_unique rfl hyi hy).trans (lat1_eq _ _).symm)
end ULHC
