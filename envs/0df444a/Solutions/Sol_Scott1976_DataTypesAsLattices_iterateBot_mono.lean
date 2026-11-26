-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.iterateBot_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:00.186963+00:00
-- url     : https://prove2.me/submissions/413ea0ad-d169-4838-adfd-5c9ee8dbdcd7

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∀ n, iterateBot f n ⊆ iterateBot f (n + 1)
  | 0 => by
    simp [iterateBot, botElem]
  | n + 1 =>
    isScottContinuous_monotone hf (solution hf n)
end Scott1976.DataTypesAsLattices
