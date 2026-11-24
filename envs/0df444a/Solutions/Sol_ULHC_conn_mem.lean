-- Prove2me | solution 1 for ULHC.conn_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:42.974806+00:00
-- url     : https://prove2.me/submissions/69f8e359-f8d3-4f39-a126-f2d113d4b538

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_Conn_refl


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) {a z : Pt} (ha : a ∈ V)
    (h : Conn F a z) : z ∈ V := by
  induction h with
  | refl => exact ha
  | tail _ hyz _ =>
    obtain ⟨e, he, h⟩ := hyz
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ <;> rw [← h]
    · exact (hV e he).2
    · exact (hV e he).1
end ULHC
