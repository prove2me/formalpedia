-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.funOf_monotone_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:54.584801+00:00
-- url     : https://prove2.me/submissions/abdaf808-2374-4204-9c83-11342a9de8e8

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {u v : Pomega} (h : u ⊆ v) (x : Pomega) :
    funOf u x ⊆ funOf v x := by
  intro m hm
  obtain ⟨n, hn, hp⟩ := hm
  exact ⟨n, hn, h hp⟩
end Scott1976.DataTypesAsLattices
