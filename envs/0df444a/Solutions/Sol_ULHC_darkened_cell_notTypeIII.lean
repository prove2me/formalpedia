-- Prove2me | solution 1 for ULHC.darkened_cell_notTypeIII
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:34.193602+00:00
-- url     : https://prove2.me/submissions/a5db11a4-4af8-46b2-8d7a-f01604335b96

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_cell_of_side
import Theorems.Thm_ULHC_notTypeIII_of_not_alt
import Theorems.Thm_ULHC_not_alt_after
import Theorems.Thm_ULHC_start_notTypeIII
import Theorems.Thm_ULHC_lateral_even_not_alt
import Theorems.Thm_ULHC_beyond_not_alt
import Theorems.Thm_ULHC_darkened
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
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
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution (hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} {e : Edge}
    (he1 : e ∈ flipCol F c s (k + 2)) (he2 : e ∉ F) (hed : e ∈ cellE d) :
    NotTypeIII V (flipCol F c s (k + 2)) d := by
  rcases darkened hk hpat he1 he2 with ⟨j, hj, hje, h | h⟩ | h
  · rw [h, lat1_eq] at hed
    rcases cell_of_side _ hed with rfl | rfl
    · rcases j with _ | j
      · rw [cellJ_zero]; exact start_notTypeIII hF hT hk hcell hpat hsep
      · exact notTypeIII_of_not_alt (not_alt_after hk hpat (by omega) (by omega))
    · exact notTypeIII_of_not_alt (lateral_even_not_alt hF hk hcell hpat hj hje).1
  · rw [h, lat2_eq] at hed
    rcases cell_of_side _ hed with rfl | rfl
    · rcases j with _ | j
      · rw [cellJ_zero]; exact start_notTypeIII hF hT hk hcell hpat hsep
      · exact notTypeIII_of_not_alt (not_alt_after hk hpat (by omega) (by omega))
    · exact notTypeIII_of_not_alt (lateral_even_not_alt hF hk hcell hpat hj hje).2
  · rw [h] at hed
    simp only [front] at hed
    rcases cell_of_side _ hed with rfl | rfl
    · exact notTypeIII_of_not_alt (not_alt_after hk hpat (by omega) le_rfl)
    · rw [nb_cellJ]; exact notTypeIII_of_not_alt (beyond_not_alt hk hpat hγ)
end ULHC
