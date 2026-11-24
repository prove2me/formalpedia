-- Prove2me | solution 1 for ULHC.lateral_even_not_alt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:09.665297+00:00
-- url     : https://prove2.me/submissions/0fb91bf5-17ba-496e-889c-8db5c21ce9a3

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_lat1_side_nb
import Theorems.Thm_ULHC_lat2_side_nb
import Theorems.Thm_ULHC_outer1_side_nb
import Theorems.Thm_ULHC_outer2_side_nb
import Theorems.Thm_ULHC_outer1_not_mem
import Theorems.Thm_ULHC_outer2_not_mem
import Theorems.Thm_ULHC_latB_eq_opp
import Theorems.Thm_ULHC_mem_after
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_lat2_after
import Theorems.Thm_ULHC_alt_adj
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_nOn_zero
import Theorems.Thm_ULHC_nb_cellJ
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hk hcell hpat
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k) (hje : j % 2 = 0) :
    ¬ Alt (flipCol F c s (k + 2)) (nb (cellJ c s j) (latA s)) ∧
      ¬ Alt (flipCol F c s (k + 2)) (nb (cellJ c s j) (latB s)) := by
  have hcj := hcell j (by omega)
  obtain ⟨_, _, f1V, f2V⟩ := isCell_corners hcj s
  have d1 := deg_front1 (cellJ c s j) s F
  have d2 := deg_front2 (cellJ c s j) s F
  rw [hF.2 _ f1V] at d1
  rw [hF.2 _ f2V] at d2
  rw [nb_cellJ] at d1 d2
  have l1 : lat1 (cellJ c s j) s ∉ F := fun h => by
    have := (hpat.2.1 j (by omega)).1.1 h; omega
  have l2 : lat2 (cellJ c s j) s ∉ F := fun h => by
    have := (hpat.2.1 j (by omega)).2.1 h; omega
  have fr : front (cellJ c s j) s ∉ F := fun h => by
    have := (hpat.2.2 j (by omega)).1 h
    have q : j + 1 < k + 2 := by omega
    simp only [q, iff_true] at this; omega
  have n1 : lat1 (cellJ c s (j + 1)) s ∈ F := (hpat.2.1 (j + 1) (by omega)).1.2 (by omega)
  have n2 : lat2 (cellJ c s (j + 1)) s ∈ F := (hpat.2.1 (j + 1) (by omega)).2.2 (by omega)
  have i0 : ∀ e, e ∉ F → ind F e = 0 := fun e h => by simp [ind, h]
  have i1 : ∀ e, e ∈ F → ind F e = 1 := fun e h => by simp [ind, h]
  rw [i0 _ l1, i0 _ fr, i1 _ n1] at d1
  rw [i0 _ l2, i0 _ fr, i1 _ n2] at d2
  have o1 : outer1 (cellJ c s j) s ∈ F := by
    by_contra h; rw [i0 _ h] at d1; omega
  have o2 : outer2 (cellJ c s j) s ∈ F := by
    by_contra h; rw [i0 _ h] at d2; omega
  -- After the flip: the lateral side is dark and the outer edge is unchanged.
  have o1' : outer1 (cellJ c s j) s ∈ flipCol F c s (k + 2) := by
    rw [mem_after, nOn_zero c s (fun m _ => outer1_not_mem c s j m)]; simp [o1]
  have o2' : outer2 (cellJ c s j) s ∈ flipCol F c s (k + 2) := by
    rw [mem_after, nOn_zero c s (fun m _ => outer2_not_mem c s j m)]; simp [o2]
  have l1' := (lat1_after hk hpat (j := j) (by omega)).2 hje
  have l2' := (lat2_after hk hpat (j := j) (by omega)).2 hje
  constructor
  · intro ha
    have := (alt_adj ha s).2
    rw [latB_eq_opp, ← lat1_side_nb, ← outer1_side_nb] at this
    exact (this.1 o1') l1'
  · intro ha
    have := (alt_adj ha s).1
    have e : latA s = (latB s).opp := by cases s <;> rfl
    rw [e, ← lat2_side_nb, ← outer2_side_nb] at this
    exact (this.1 o2') l2'
end ULHC
