-- Prove2me | solution 1 for ULHC.Tsw_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:56:40.291811+00:00
-- url     : https://prove2.me/submissions/0d0637e1-e156-4cdc-a550-0ae05807bd60

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
import Theorems.Thm_ULHC_sidesIn_insert
import Theorems.Thm_ULHC_ite_or_ne
import Theorems.Thm_ULHC_nb_comm_lat
import Theorems.Thm_ULHC_Tsw_distinct
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_nb_ne
import Theorems.Thm_ULHC_outer1_side_nb
import Theorems.Thm_ULHC_outer2_side_nb
import Theorems.Thm_ULHC_side_mem_cellE_iff
import Theorems.Thm_ULHC_sidesIn_single
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (j : ℕ) (x : Pt) : sidesIn (Tsw c s j) x % 2 = 0 := by
  have l1 := lat1_eq (cellJ c s j) s
  have l2 := lat2_eq (cellJ c s j) s
  have l3 := lat1_eq (cellJ c s (j + 1)) s
  have l4 := lat2_eq (cellJ c s (j + 1)) s
  have o1 := outer1_side_nb (cellJ c s j) s
  have o2 := outer2_side_nb (cellJ c s j) s
  have n1 := nb_comm_lat c s j
  -- the six sides are distinct
  have d := Tsw_distinct c s j
  obtain ⟨d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := d
  unfold Tsw
  rw [sidesIn_insert _ _ _ (by simp [d12, d13, d14, d15, d16]),
    sidesIn_insert _ _ _ (by simp [d23, d24, d25, d26]),
    sidesIn_insert _ _ _ (by simp [d34, d35, d36]),
    sidesIn_insert _ _ _ (by simp [d45, d46]),
    sidesIn_insert _ _ _ (by simp [d56]), sidesIn_single]
  rw [l1, l2, l3, l4, o1, o2]
  simp only [side_mem_cellE_iff]
  rw [n1.1, n1.2]
  have e1 : nb (cellJ c s j) (latA s) ≠ nb (cellJ c s (j + 1)) (latA s) := by
    rw [← n1.1]; exact nb_ne _ _
  have e2 : nb (cellJ c s j) (latB s) ≠ nb (cellJ c s (j + 1)) (latB s) := by
    rw [← n1.2]; exact nb_ne _ _
  rw [ite_or_ne (nb_ne _ _), ite_or_ne (nb_ne _ _), ite_or_ne (nb_ne _ _), ite_or_ne (nb_ne _ _),
    ite_or_ne e1, ite_or_ne e2]
  omega
end ULHC
