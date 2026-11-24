-- Prove2me | solution 1 for ULHC.TF.deg_insert_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:23.232824+00:00
-- url     : https://prove2.me/submissions/ad0d4185-e386-4536-9fa3-d6e9e0d13bd6

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∉ F) {z : Pt} (hz : e.p = z ∨ e.q = z) :
    deg (insert e F) z = deg F z + 1 := by
  rw [deg_insert he, if_pos hz]
end ULHC.TF
