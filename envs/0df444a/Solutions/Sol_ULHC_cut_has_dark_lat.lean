-- Prove2me | solution 1 for ULHC.cut_has_dark_lat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:09:27.743787+00:00
-- url     : https://prove2.me/submissions/b82b5591-4d9b-4bf0-ba08-70bb057eb231

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_Border_not_cut
import Theorems.Thm_ULHC_Border_same_side
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_alt_corners_conn
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_back1_nb
import Theorems.Thm_ULHC_back2_nb
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_conn_mem
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_ind_le_one
import Theorems.Thm_ULHC_isCell_corners
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P) (hT : NoTypeIII V F)
include hF hB hT
namespace ULHC
theorem _root_.solution {w : Pt} (hw : IsCell V w) (s : Side) (hcut : Cut P (sideEdge w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  by_contra hn
  push Not at hn
  obtain ⟨n1, n2⟩ := hn
  rw [← lat1_eq] at n1
  rw [← lat2_eq] at n2
  have hfr : front w s ∉ F := fun h => hB.not_cut h hcut
  -- Forcing at the two front corners.
  obtain ⟨wb1, wb2, wf1, wf2⟩ := isCell_corners hw s
  have d1 := deg_front1 w s F
  have d2 := deg_front2 w s F
  rw [hF.2 _ wf1] at d1
  rw [hF.2 _ wf2] at d2
  have i1 : ind F (lat1 w s) = 0 := by simp [ind, n1]
  have i2 : ind F (lat2 w s) = 0 := by simp [ind, n2]
  have i3 : ind F (front w s) = 0 := by simp [ind, hfr]
  have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
    intro e h; unfold ind at h; split_ifs at h with h'; exact h'
  rw [i1, i3] at d1
  rw [i2, i3] at d2
  have l1 : lat1 (nb w s) s ∈ F := by
    have := ind_le_one F (lat1 (nb w s) s)
    have := ind_le_one F (outer1 w s)
    exact mem1 _ (by omega)
  have l2 : lat2 (nb w s) s ∈ F := by
    have := ind_le_one F (lat2 (nb w s) s)
    have := ind_le_one F (outer2 w s)
    exact mem1 _ (by omega)
  set r := nb w s
  have c1 : Conn F (back1 r s) (front1 r s) := (ends_lat1 r s).conn l1
  have c2 : Conn F (back2 r s) (front2 r s) := (ends_lat2 r s).conn l2
  have rf1 : front1 r s ∈ V := conn_mem hF.1 (by rw [back1_nb]; exact wf1) c1
  have rf2 : front2 r s ∈ V := conn_mem hF.1 (by rw [back2_nb]; exact wf2) c2
  have hr : IsCell V r := isCell_of_corners r s (by rw [back1_nb]; exact wf1)
    (by rw [back2_nb]; exact wf2) rf1 rf2
  -- The two front corners of `w` are joined, so the front is not cut.
  have hjoin : Conn F (back1 r s) (back2 r s) := by
    by_cases hf : front r s ∈ F
    · exact (c1.trans ((ends_front r s).conn hf)).trans c2.symm
    · have hbk : back r s ∉ F := by rw [back_nb]; exact hfr
      have ha : Alt F r := by
        rw [lat1_eq] at l1
        rw [lat2_eq] at l2
        simp only [back, front, sideEdge] at hbk hf
        obtain ⟨x, y⟩ := r
        cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 hbk hf <;> unfold Alt <;>
          tauto
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn hT hr ha
      obtain ⟨x, y⟩ := r
      cases s <;> simp only [back1, back2] at * <;>
        first
        | exact k1
        | exact k2.symm.trans k3
        | exact k1.symm.trans k3
        | exact k2
  rw [back1_nb, back2_nb] at hjoin
  apply hcut |> fun h => ?_
  have := hB.same_side hjoin
  have hends := ends_front w s
  unfold Cut at hcut
  rcases hends with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp only [front] at q1 q2 <;> rw [q1, q2] at hcut <;>
    tauto
end ULHC
