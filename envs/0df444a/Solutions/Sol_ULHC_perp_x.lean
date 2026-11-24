-- Prove2me | solution 1 for ULHC.perp_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:36:12.142512+00:00
-- url     : https://prove2.me/submissions/2a8c9f07-2b7d-4b6b-b374-523ce8f7b55a

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {d u : Pt} {tf tu : Side} {x : Edge}
  (hb : back d tf ∈ F) (hxd : x ∈ F) (hxlat : x = lat1 d tf ∨ x = lat2 d tf)
  (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F))
  (lu1 : lat1 u tu ∈ F) (lu2 : lat2 u tu ∈ F) (bu : back u tu ∉ F) (fu : front u tu ∉ F)
  (hxu : x ∈ cellE u) (hdu : d ≠ u)
include hxlat
namespace ULHC
theorem _root_.solution (ht : tf = latA s ∨ tf = latB s) : x = back d s ∨ x = front d s := by
  rcases ht with rfl | rfl
  · rcases (frame_latA d s).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hxlat with rfl | rfl <;> tauto
  · rcases (frame_latB d s).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hxlat with rfl | rfl <;> tauto
end ULHC
