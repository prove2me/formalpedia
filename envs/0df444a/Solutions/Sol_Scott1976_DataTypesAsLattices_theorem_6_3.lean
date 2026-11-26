-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_6_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:36.245131+00:00
-- url     : https://prove2.me/submissions/cd1804fa-cf68-4c30-b8bb-1ca22684b78f

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
theorem _root_.solution {f : Pomega → Pomega} (_hf : IsScottContinuous f) :
    {x | f x = topElem} = ⋂ n, {x | n ∈ f x} := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    have hfx : f x = topElem := hx
    simp [hfx]
  · intro hx
    ext k
    constructor
    · intro _; trivial
    · intro _
      exact Set.mem_iInter.mp hx k
end Scott1976.DataTypesAsLattices
