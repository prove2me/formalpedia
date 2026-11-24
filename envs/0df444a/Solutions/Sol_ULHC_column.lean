-- Prove2me | solution 1 for ULHC.column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:26:29.129267+00:00
-- url     : https://prove2.me/submissions/30224946-c652-4047-ae69-6b6d33a08790

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_front_out
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Good_isCell
import Theorems.Thm_ULHC_Good_step
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_ind_le_one
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_nb_cellJ
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
include hF hH hs
namespace ULHC
theorem _root_.solution {w : Pt} {s : Side} {o : Bool} (hp : ParOK w s o)
    (_hb : back w s ∈ F) (hl1 : lat1 w s ∉ F) (hl2 : lat2 w s ∉ F) (hg : Good o (D F H w)) :
    ∀ J, (∀ j < J, front (cellJ w s j) s ∈ F ↔ j % 2 = 1) →
      (∀ j ≤ J, (lat1 (cellJ w s j) s ∈ F ↔ j % 2 = 1) ∧
        (lat2 (cellJ w s j) s ∈ F ↔ j % 2 = 1)) ∧
      ∀ j ≤ J, Good o (D F H (cellJ w s j)) := by
  intro J
  induction J with
  | zero =>
    intro _
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero]; simp [hl1, hl2]
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero]; exact hg
  | succ J ih =>
    intro hc
    obtain ⟨hlat, hgood⟩ := ih (fun j hj => hc j (by omega))
    have hfJ := hc J (by omega)
    have hgJ := hgood J le_rfl
    have hcJ : IsCell V (cellJ w s J) := Good.isCell hF hH hs hgJ
    obtain ⟨_, _, f1V, f2V⟩ := isCell_corners hcJ s
    have d1 := deg_front1 (cellJ w s J) s F
    have d2 := deg_front2 (cellJ w s J) s F
    rw [hF.2 _ f1V] at d1
    rw [hF.2 _ f2V] at d2
    rw [nb_cellJ] at d1 d2
    have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
      intro e h; unfold ind at h; split_ifs at h with h'; exact h'
    have nmem : ∀ e, ind F e = 0 → e ∉ F := by
      intro e h he; simp [ind, he] at h
    have i_of : ∀ e, ∀ p : Prop, (e ∈ F ↔ p) → p → ind F e = 1 := by
      intro e p h hp; unfold ind; rw [if_pos (h.2 hp)]
    have i_of' : ∀ e, ∀ p : Prop, (e ∈ F ↔ p) → ¬ p → ind F e = 0 := by
      intro e p h hp; unfold ind; rw [if_neg (fun h' => hp (h.1 h'))]
    have b1 := ind_le_one F (lat1 (cellJ w s (J + 1)) s)
    have b2 := ind_le_one F (lat2 (cellJ w s (J + 1)) s)
    have b3 := ind_le_one F (outer1 (cellJ w s J) s)
    have b4 := ind_le_one F (outer2 (cellJ w s J) s)
    have newlat : (lat1 (cellJ w s (J + 1)) s ∈ F ↔ (J + 1) % 2 = 1) ∧
        (lat2 (cellJ w s (J + 1)) s ∈ F ↔ (J + 1) % 2 = 1) := by
      rcases Nat.mod_two_eq_zero_or_one J with h | h
      · have a1 := i_of' _ _ (hlat J le_rfl).1 (by omega)
        have a2 := i_of' _ _ (hlat J le_rfl).2 (by omega)
        have a3 := i_of' _ _ hfJ (by omega)
        rw [a1, a3] at d1
        rw [a2, a3] at d2
        have q : (J + 1) % 2 = 1 := by omega
        exact ⟨⟨fun _ => q, fun _ => mem1 _ (by omega)⟩, ⟨fun _ => q, fun _ => mem1 _ (by omega)⟩⟩
      · have a1 := i_of _ _ (hlat J le_rfl).1 (by omega)
        have a2 := i_of _ _ (hlat J le_rfl).2 (by omega)
        have a3 := i_of _ _ hfJ (by omega)
        rw [a1, a3] at d1
        rw [a2, a3] at d2
        have q : ¬ (J + 1) % 2 = 1 := by omega
        exact ⟨⟨fun h' => absurd h' (nmem _ (by omega)), fun h' => absurd h' q⟩,
          ⟨fun h' => absurd h' (nmem _ (by omega)), fun h' => absurd h' q⟩⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases (show j ≤ J ∨ j = J + 1 by omega) with h | rfl
      · exact hlat j h
      · exact newlat
    · rcases (show j ≤ J ∨ j = J + 1 by omega) with h | rfl
      · exact hgood j h
      · rw [← nb_cellJ]
        exact Good.step hF hH (front_out hp J hfJ) hgJ
end ULHC
