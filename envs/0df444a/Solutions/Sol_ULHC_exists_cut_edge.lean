-- Prove2me | solution 1 for ULHC.exists_cut_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:52.437599+00:00
-- url     : https://prove2.me/submissions/fdcdfa80-4684-4903-ba54-99d09c8ac313

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_Conn_refl


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {H : Finset Edge} {P : Finset Pt} {x y : Pt} (h : Conn H x y)
    (hx : x ∈ P) (hy : y ∉ P) : ∃ e ∈ H, Cut P e := by
  induction h with
  | refl => exact absurd hx hy
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ P
    · obtain ⟨e, he, h⟩ := hbc
      refine ⟨e, he, ?_⟩
      unfold Cut
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
    · exact ih hb
end ULHC
