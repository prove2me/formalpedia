-- Prove2me | solution 1 for ULHC.Ends.deg_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:12.475447+00:00
-- url     : https://prove2.me/submissions/a562631f-c514-41fd-a569-5c768530ee19

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_deg_erase


set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution {F : Finset Edge} (h : Ends e u v) (he : e ∈ F) (z : Pt) :
    deg (F.erase e) z + (if z = u ∨ z = v then 1 else 0) = deg F z := by
  have := ULHC.deg_erase he z
  by_cases hz : z = u ∨ z = v
  · rw [if_pos ((h.inc_iff z).2 hz)] at this; rw [if_pos hz]; exact this
  · rw [if_neg (fun h' => hz ((h.inc_iff z).1 h'))] at this; rw [if_neg hz]; exact this
end Ends
end ULHC
