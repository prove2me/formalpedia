-- Prove2me | solution 1 for ULHC.adj_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:36.442095+00:00
-- url     : https://prove2.me/submissions/df6dffdf-f8c4-4531-808c-5115ff0e8cbd

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∈ F) {y : Pt} (hy : e.p = y ∨ e.q = y) :
    Adj F y (other e y) := by
  unfold other
  split_ifs with h
  · exact ⟨e, he, Or.inl ⟨h, rfl⟩⟩
  · rcases hy with hy | hy
    · exact absurd hy h
    · exact ⟨e, he, Or.inr ⟨rfl, hy⟩⟩
end ULHC
