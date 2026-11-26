-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.funOf_monotone_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:53.615783+00:00
-- url     : https://prove2.me/submissions/4edbc63e-92ec-4473-a9df-f142219bd7cd

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u : Pomega) {x y : Pomega} (h : x ⊆ y) :
    funOf u x ⊆ funOf u y := by
  intro m hm
  obtain ⟨n, hn, hp⟩ := hm
  exact ⟨n, subset_trans hn h, hp⟩
end Scott1976.DataTypesAsLattices
