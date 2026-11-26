-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.isScottContinuous_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:42.552966+00:00
-- url     : https://prove2.me/submissions/78263665-15ac-40c1-b2b3-dd73425f005d

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega}
    (hf : IsScottContinuous f) {x y : Pomega} (h : x ⊆ y) : f x ⊆ f y := by
  intro m hm
  rw [hf x, mem_scottUnion] at hm
  rw [hf y, mem_scottUnion]
  obtain ⟨n, hn, hmn⟩ := hm
  exact ⟨n, subset_trans hn h, hmn⟩
end Scott1976.DataTypesAsLattices
