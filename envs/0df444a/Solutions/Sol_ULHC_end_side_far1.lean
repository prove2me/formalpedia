-- Prove2me | solution 1 for ULHC.end_side_far1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:09:28.196617+00:00
-- url     : https://prove2.me/submissions/a97652fe-e153-4db3-bb7f-e4c5d6434d00

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_back2_not_side_corner
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_four_sides_class
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_side_back2
import Theorems.Thm_ULHC_side_back_ends
import Theorems.Thm_ULHC_side_back_next
import Theorems.Thm_ULHC_side_front
import Theorems.Thm_ULHC_side_front2
import Theorems.Thm_ULHC_side_front_ends
import Theorems.Thm_ULHC_side_lat2


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hT hk hcell hpat
namespace ULHC
theorem _root_.solution (hb : outer1 (cellJ c s k) s ∈ F) (hf : outer1 (cellJ c s (k + 1)) s ∈ F) :
    lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F := by
  intro hl
  set u := cellJ c s (k + 1)
  set L := nb u (latA s)
  have hbL : back L s ∈ F := by
    rw [show back L s = outer1 (cellJ c s k) s by rw [← side_back_next, nb_cellJ]]; exact hb
  have hfL : front L s ∈ F := by rw [side_front]; exact hf
  have hnL : lat2 L s ∈ F := by
    rw [side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
  have hV1 := (side_back_ends u s).inV (hF.1 _ hbL)
  have hV2 := (side_front_ends u s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hV1.1 ?_ hV2.1 ?_
    · rw [side_back2]; exact hV1.2
    · rw [side_front2]; exact hV2.2
  have hz : Conn F (back1 L s) (back2 u s) :=
    ((side_back_ends u s).conn hbL).trans (end_same hT hk hcell hpat)
  exact back2_not_side_corner u s (four_sides_class hF hcL s hbL hfL hl hnL hz)
end ULHC
