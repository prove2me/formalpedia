-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.typicalGdelta_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:57.079191+00:00
-- url     : https://prove2.me/submissions/96b90081-8d81-432a-90cc-718e58230326

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution : typicalGdelta = ⋂ n, {x : Pomega | n ∈ x} := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    have hx' : x = topElem := hx
    simp [hx']
  · intro hx
    ext k
    constructor
    · intro _; trivial
    · intro _
      exact Set.mem_iInter.mp hx k
end Scott1976.DataTypesAsLattices
