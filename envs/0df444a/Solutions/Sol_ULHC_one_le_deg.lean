-- Prove2me | solution 1 for ULHC.one_le_deg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:39.798972+00:00
-- url     : https://prove2.me/submissions/ba9eab4a-e10c-4a3b-9a1a-08c25c720674

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_deg_erase

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∈ F) {y : Pt} (hy : e.p = y ∨ e.q = y) :
    1 ≤ deg F y := by
  have := deg_erase he y
  rw [if_pos hy] at this
  omega
end ULHC
