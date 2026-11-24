-- Prove2me | solution 1 for ULHC.end_side_far2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:09:28.66781+00:00
-- url     : https://prove2.me/submissions/e15fab71-49a4-4dde-962d-937980350b31

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_back1_not_side2_corner
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_four_sides_class
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side2_back1
import Theorems.Thm_ULHC_side2_back_ends
import Theorems.Thm_ULHC_side2_front
import Theorems.Thm_ULHC_side2_front1
import Theorems.Thm_ULHC_side2_front_ends
import Theorems.Thm_ULHC_side2_lat1


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
theorem _root_.solution (hb : outer2 (cellJ c s k) s ∈ F) (hf : outer2 (cellJ c s (k + 1)) s ∈ F) :
    lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F := by
  intro hl
  set u := cellJ c s (k + 1)
  set L := nb u (latB s)
  have hbL : back L s ∈ F := by
    rw [show back L s = outer2 (cellJ c s k) s by rw [outer2_side_nb_next, nb_cellJ]; rfl]
    exact hb
  have hfL : front L s ∈ F := by rw [side2_front]; exact hf
  have hnL : lat1 L s ∈ F := by
    rw [side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have hV1 := (side2_back_ends u s).inV (hF.1 _ hbL)
  have hV2 := (side2_front_ends u s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ hV1.2 ?_ hV2.2
    · rw [side2_back1]; exact hV1.1
    · rw [side2_front1]; exact hV2.1
  have hz : Conn F (back1 L s) (back1 u s) := by
    rw [side2_back1]; exact (end_same hT hk hcell hpat).symm
  exact back1_not_side2_corner u s (four_sides_class hF hcL s hbL hfL hnL hl hz)
end ULHC
