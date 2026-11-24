-- Prove2me | solution 1 for ULHC.mid_not_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:10.336065+00:00
-- url     : https://prove2.me/submissions/129296c4-0602-4968-9e5a-2c6edda4449d

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_cell_of_side
import Theorems.Thm_ULHC_notTypeIII_of_not_alt
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_lat2_after
import Theorems.Thm_ULHC_front_after
import Theorems.Thm_ULHC_not_alt_after
import Theorems.Thm_ULHC_lateral_even_not_alt
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back1_cellJ_succ
import Theorems.Thm_ULHC_back2_nb
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_front_mem_self
import Theorems.Thm_ULHC_inc_of_deg_two
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_lat2_not_mem
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
theorem _root_.solution (_hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} {e : Edge} {z : Pt}
    (hz : IsMid c s k z) (he : e ∈ flipCol F c s (k + 2)) (hez : e.p = z ∨ e.q = z)
    (hed : e ∈ cellE d) : NotTypeIII V (flipCol F c s (k + 2)) d := by
  obtain ⟨j, hjo, hjk, hzj⟩ := hz
  have hF' : Deg2 V (flipCol F c s (k + 2)) := deg2_flipCol _ F hF hpat (fun j hj => hcell j (by omega))
  have hfr : front (cellJ c s j) s ∈ flipCol F c s (k + 2) := (front_after hk hpat (by omega)).2 hjo
  have nmid : ∀ m, 1 ≤ m → m ≤ k + 1 → NotTypeIII V (flipCol F c s (k + 2)) (cellJ c s m) :=
    fun m h1 h2 => notTypeIII_of_not_alt (not_alt_after hk hpat h1 h2)
  have hfrc : ∀ d', front (cellJ c s j) s ∈ cellE d' →
      NotTypeIII V (flipCol F c s (k + 2)) d' := by
    intro d' h
    simp only [front] at h
    rcases cell_of_side _ h with rfl | rfl
    · exact nmid j (by omega) (by omega)
    · rw [nb_cellJ]; exact nmid (j + 1) (by omega) (by omega)
  rcases hzj with rfl | rfl
  · -- `z = front1 c_j`: its two edges after the flip are `front c_j` and `lat1 c_(j+1)`.
    have hl : lat1 (cellJ c s (j + 1)) s ∈ flipCol F c s (k + 2) :=
      (lat1_after hk hpat (by omega)).2 (by omega)
    have zV : front1 (cellJ c s j) s ∈ V := (isCell_corners (hcell j (by omega)) s).2.2.1
    have e1 : (front (cellJ c s j) s).p = front1 (cellJ c s j) s ∨
        (front (cellJ c s j) s).q = front1 (cellJ c s j) s :=
      ((ends_front _ s).inc_iff _).2 (Or.inl rfl)
    have e2 : (lat1 (cellJ c s (j + 1)) s).p = front1 (cellJ c s j) s ∨
        (lat1 (cellJ c s (j + 1)) s).q = front1 (cellJ c s j) s := by
      have := ends_lat1 (cellJ c s (j + 1)) s
      rw [back1_cellJ_succ] at this
      exact (this.inc_iff _).2 (Or.inl rfl)
    have hne : front (cellJ c s j) s ≠ lat1 (cellJ c s (j + 1)) s := by
      intro h
      have := front_mem_self c s j
      exact absurd (h ▸ this) (lat1_not_mem c s (j := j + 1) (m := j) (by omega))
    rcases inc_of_deg_two (hF'.2 _ zV) hfr e1 hl e2 hne he hez with rfl | rfl
    · exact hfrc d hed
    · rw [lat1_eq] at hed
      rcases cell_of_side _ hed with rfl | rfl
      · exact nmid (j + 1) (by omega) (by omega)
      · exact notTypeIII_of_not_alt
          (lateral_even_not_alt hF hk hcell hpat (j := j + 1) (by omega) (by omega)).1
  · have hl : lat2 (cellJ c s (j + 1)) s ∈ flipCol F c s (k + 2) :=
      (lat2_after hk hpat (by omega)).2 (by omega)
    have zV : front2 (cellJ c s j) s ∈ V := (isCell_corners (hcell j (by omega)) s).2.2.2
    have e1 : (front (cellJ c s j) s).p = front2 (cellJ c s j) s ∨
        (front (cellJ c s j) s).q = front2 (cellJ c s j) s :=
      ((ends_front _ s).inc_iff _).2 (Or.inr rfl)
    have e2 : (lat2 (cellJ c s (j + 1)) s).p = front2 (cellJ c s j) s ∨
        (lat2 (cellJ c s (j + 1)) s).q = front2 (cellJ c s j) s := by
      have := ends_lat2 (cellJ c s (j + 1)) s
      have hb : back2 (cellJ c s (j + 1)) s = front2 (cellJ c s j) s := by
        rw [← nb_cellJ, back2_nb]
      rw [hb] at this
      exact (this.inc_iff _).2 (Or.inl rfl)
    have hne : front (cellJ c s j) s ≠ lat2 (cellJ c s (j + 1)) s := by
      intro h
      have := front_mem_self c s j
      exact absurd (h ▸ this) (lat2_not_mem c s (j := j + 1) (m := j) (by omega))
    rcases inc_of_deg_two (hF'.2 _ zV) hfr e1 hl e2 hne he hez with rfl | rfl
    · exact hfrc d hed
    · rw [lat2_eq] at hed
      rcases cell_of_side _ hed with rfl | rfl
      · exact nmid (j + 1) (by omega) (by omega)
      · exact notTypeIII_of_not_alt
          (lateral_even_not_alt hF hk hcell hpat (j := j + 1) (by omega) (by omega)).2
end ULHC
