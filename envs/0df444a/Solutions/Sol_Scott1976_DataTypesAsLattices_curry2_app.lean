-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.curry2_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:18.96206+00:00
-- url     : https://prove2.me/submissions/43d59e61-7d0e-4478-8ba5-b483d86580e7

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_const_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (f : Pomega → Pomega → Pomega)
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) (x y : Pomega) :
    funOf (funOf (curry2 f hfx hfy) x) y = f x y := by
  have h1 : funOf (curry2 f hfx hfy) x = graph (fun y => f x y) :=
    beta (graph_const_isScottContinuous f hfx) x
  rw [h1]
  exact beta (hfy x) y
end Scott1976.DataTypesAsLattices
