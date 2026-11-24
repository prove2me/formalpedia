-- Prove2me | solution 1 for ULHC.phase2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:28:20.158531+00:00
-- url     : https://prove2.me/submissions/a6d316bf-275d-419f-82c1-1abc0c7cbe02

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_horiz_latA
import Theorems.Thm_ULHC_horiz_latB
import Theorems.Thm_ULHC_exists_not_cell
import Theorems.Thm_ULHC_column
import Theorems.Thm_ULHC_Border_same_side
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Good_isCell
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_latA_opp
import Theorems.Thm_ULHC_latB_opp
import Theorems.Thm_ULHC_opp_opp
import Theorems.Thm_ULHC_outArc_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P)
include hF hH hs hB
namespace ULHC
theorem _root_.solution {w : Pt} {o : Bool} (hg : Good o (D F H w)) (hst : Stop F P o w) :
    ∃ s n, 2 ≤ n ∧ StripPat F w s n ∧ (∀ j < n, IsCell V (cellJ w s j)) ∧
      (∀ j < n, Good o (D F H (cellJ w s j))) ∧ ParOK w s o ∧
      ¬ Conn F (back1 w s) (front1 w s) := by
  obtain ⟨d, hd, hdo, hla, hlb, ⟨si, hsi, hcut, hin⟩, hnc, hout⟩ := hst
  set s := d.opp
  have hb : back w s ∈ F := by simp only [back, s, opp_opp]; exact hd
  have hf0 : front w s ∉ F := hdo
  have hl1 : lat1 w s ∉ F := by rw [lat1_eq, latA_opp]; exact hla
  have hl2 : lat2 w s ∉ F := by rw [lat2_eq, latB_opp]; exact hlb
  -- Parity from the entry side.
  have hp : ParOK w s o := by
    unfold ParOK
    rw [outArc_eq] at hin
    have hsiF : sideEdge w si ∉ F := by rcases hsi with rfl | rfl <;> assumption
    have hh : si.horiz = !s.horiz := by
      rcases hsi with rfl | rfl
      · rw [← horiz_latA, latA_opp]
      · rw [← horiz_latB, latB_opp]
    rw [hh] at hin
    simp only [hsiF, decide_false] at hin
    cases hs' : s.horiz <;> cases o <;> cases hq : par w <;> simp_all
  -- Opposite sides of the border.
  have hsep : ¬ Conn F (back1 w s) (front1 w s) := by
    intro hc
    have e1 := hB.same_side hc
    have e2 := hB.same_side ((ends_back w s).conn hb)
    have hfc : ¬ Cut P (front w s) := hnc
    have ef := ends_front w s
    unfold Cut at hfc
    have e3 : front1 w s ∈ P ↔ front2 w s ∈ P := by
      rcases ef with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hfc <;> tauto
    rcases hsi with rfl | rfl
    · have := ends_lat1 w s
      rw [lat1_eq, latA_opp] at this
      unfold Cut at hcut
      rcases this with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut <;> tauto
    · have := ends_lat2 w s
      rw [lat2_eq, latB_opp] at this
      unfold Cut at hcut
      rcases this with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut <;> tauto
  -- The first cell where the pattern stops continuing.
  obtain ⟨J0, hJ0⟩ := exists_not_cell V w s
  have hex : ∃ J, ¬ (front (cellJ w s J) s ∈ F ↔ J % 2 = 1) := by
    by_contra hall
    push Not at hall
    obtain ⟨_, hgd⟩ := column hF hH hs hp hb hl1 hl2 hg (J0 + 1) (fun j _ => hall j)
    exact hJ0 (Good.isCell hF hH hs (hgd J0 (by omega)))
  set J := Nat.find hex
  have hJ : ¬ (front (cellJ w s J) s ∈ F ↔ J % 2 = 1) := Nat.find_spec hex
  have hbefore : ∀ j < J, front (cellJ w s j) s ∈ F ↔ j % 2 = 1 := fun j hj => by
    have := Nat.find_min hex hj; push Not at this; exact this
  have hJpos : J ≠ 0 := by
    intro h0
    apply hJ; rw [h0, cellJ_zero]; simp [hf0]
  obtain ⟨hlat, hgd⟩ := column hF hH hs hp hb hl1 hl2 hg J hbefore
  refine ⟨s, J + 1, by omega, ⟨hb, fun j hj => hlat j (by omega), fun j hj => ?_⟩,
    fun j hj => Good.isCell hF hH hs (hgd j (by omega)), fun j hj => hgd j (by omega), hp, hsep⟩
  rcases (show j < J ∨ j = J by omega) with h | rfl
  · have q : j + 1 < J + 1 := by omega
    simp only [q, iff_true]; exact hbefore j h
  · simp only [lt_self_iff_false, iff_false]
    by_cases hf : front (cellJ w s J) s ∈ F <;> simp_all
end ULHC
