-- Prove2me | solution 1 for ULHC.TF.deg_erase_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:12.970665+00:00
-- url     : https://prove2.me/submissions/5da3bcf5-23d2-4d60-b207-25e87e7a98be

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_Ends_deg_erase
import Theorems.Thm_ULHC_deg_erase


set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∈ F) {z : Pt} (hz : e.p = z ∨ e.q = z) :
    deg (F.erase e) z + 1 = deg F z := by
  have := deg_erase he z; rwa [if_pos hz] at this
end ULHC.TF
