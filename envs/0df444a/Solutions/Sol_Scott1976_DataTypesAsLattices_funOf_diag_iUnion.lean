-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.funOf_diag_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:11.601225+00:00
-- url     : https://prove2.me/submissions/2058b92b-fd9c-46b4-8d34-84c1085c6ed7

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous_left
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3_diag


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (d : Pomega) :
    funOf d d = ⋃ l, {m | e l ⊆ d ∧ m ∈ funOf (e l) (e l)} := by
  have h := theorem_1_3_diag (x := d)
    (f := fun u y => funOf u y)
    (fun y => funOf_isScottContinuous_left y)
    (fun u => funOf_isScottContinuous u)
  exact h
end Scott1976.DataTypesAsLattices
