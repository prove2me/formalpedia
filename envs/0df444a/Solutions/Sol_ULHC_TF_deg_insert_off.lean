-- Prove2me | solution 1 for ULHC.TF.deg_insert_off
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:30.585621+00:00
-- url     : https://prove2.me/submissions/3f95de5e-7ebf-46f4-be13-f9c7b71aa9d4

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∉ F) {z : Pt} (hz : ¬ (e.p = z ∨ e.q = z)) :
    deg (insert e F) z = deg F z := by
  rw [deg_insert he, if_neg hz, add_zero]
end ULHC.TF
