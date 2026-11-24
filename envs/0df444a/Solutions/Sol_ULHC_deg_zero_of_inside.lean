-- Prove2me | solution 1 for ULHC.deg_zero_of_inside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:17:35.514807+00:00
-- url     : https://prove2.me/submissions/16267c7b-5fee-46ad-b978-1619eb259956

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_exists_inc_of_deg


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) {z : Pt}
    (hz : z ∉ V) : deg F z = 0 := by
  by_contra h
  obtain ⟨e, he, hi⟩ := exists_inc_of_deg (F := F) (y := z) (by omega)
  rcases hi with hi | hi
  · exact hz (hi ▸ (hV e he).1)
  · exact hz (hi ▸ (hV e he).2)
end ULHC
