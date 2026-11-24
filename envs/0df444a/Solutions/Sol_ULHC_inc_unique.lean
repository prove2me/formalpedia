-- Prove2me | solution 1 for ULHC.inc_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:09.901412+00:00
-- url     : https://prove2.me/submissions/cf1796e4-67e8-47bc-91a0-057fe3fadc76

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_one_le_deg

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {y : Pt} (hd : deg F y = 1) {e e' : Edge} (he : e ∈ F)
    (hy : e.p = y ∨ e.q = y) (he' : e' ∈ F) (hy' : e'.p = y ∨ e'.q = y) : e' = e := by
  by_contra hne
  have h1 := deg_erase he y
  rw [if_pos hy] at h1
  have h2 := one_le_deg (Finset.mem_erase.2 ⟨hne, he'⟩) hy'
  omega
end ULHC
