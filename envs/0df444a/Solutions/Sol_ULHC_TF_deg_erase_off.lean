-- Prove2me | solution 1 for ULHC.TF.deg_erase_off
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:20.342939+00:00
-- url     : https://prove2.me/submissions/3e32ac66-2a67-4c38-8d54-9c61d431a732

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_Ends_deg_erase
import Theorems.Thm_ULHC_deg_erase


set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∈ F) {z : Pt} (hz : ¬ (e.p = z ∨ e.q = z)) :
    deg (F.erase e) z = deg F z := by
  have := deg_erase he z; rwa [if_neg hz, add_zero] at this
end ULHC.TF
