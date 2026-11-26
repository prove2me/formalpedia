-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.isScottOpen_isUpper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:33.051948+00:00
-- url     : https://prove2.me/submissions/b3bec213-eaee-4762-a0d5-d124671af23c

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {U : Set Pomega} (hU : IsScottOpen U)
    {x y : Pomega} (hx : x ∈ U) (hxy : x ⊆ y) : y ∈ U := by
  obtain ⟨B, rfl⟩ := hU
  obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨n, hn, subset_trans hxn hxy⟩
end Scott1976.DataTypesAsLattices
