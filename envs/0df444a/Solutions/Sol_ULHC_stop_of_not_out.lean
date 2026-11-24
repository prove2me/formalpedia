-- Prove2me | solution 1 for ULHC.stop_of_not_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:13:51.27061+00:00
-- url     : https://prove2.me/submissions/96acd720-e030-4e68-9c97-970fdb1c81db

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
import Theorems.Thm_ULHC_alt_no_cut
import Theorems.Thm_ULHC_cut_has_dark_lat
import Theorems.Thm_ULHC_step_cell


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)
include hF hB hT
namespace ULHC
theorem _root_.solution {w : Pt} (hw : IsCell V w) (he : Entered F P o w)
    (hno : ¬ Out F P o w) : Stop F P o w := by
  obtain ⟨si, hcut, hin⟩ := he
  rcases step_cell hB w o (fun s h => cut_has_dark_lat hF hB hT hw s h)
      (fun ha => alt_no_cut hB hT hw ha) si hcut hin with
    ⟨so, _, h2, h3, _⟩ | ⟨d, h1, h2, h3, h4, h5, h6, h7, _⟩
  · exact absurd ⟨so, h2, h3⟩ hno
  · exact ⟨d, h1, h2, h3, h4, ⟨si, h5, hcut, hin⟩, h6, h7⟩
end ULHC
