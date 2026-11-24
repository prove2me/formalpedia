-- Prove2me | solution 1 for ULHC.mem_flip_off
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:59.742068+00:00
-- url     : https://prove2.me/submissions/b575a75d-6fd9-4a62-a8c2-9cf3a1e53f11

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {G : Finset Edge} {u : Pt} {e : Edge} (h : e ∉ cellE u) :
    e ∈ flip G u ↔ e ∈ G := by
  rw [mem_flip_iff]; tauto
end ULHC
